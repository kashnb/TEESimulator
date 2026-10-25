package org.matrix.teesim

import android.os.Build
import java.io.File

/**
 * Finds the keystore daemon and drives the packaged `inject` binary to load the right interceptor
 * into it: `inject <pid> <lib.so> entry`. On Android 12+ the target is keystore2 with
 * libteesim_keymint.so; on 10/11 it is keystore with libteesim_keystore.so. Re-injects whenever the
 * daemon restarts (new pid).
 */
class Injector(private val moduleDir: File) {

    private val api = Build.VERSION.SDK_INT
    private val procName = if (api >= 31) "keystore2" else "keystore"
    private val libName = if (api >= 31) "libteesim_keymint.so" else "libteesim_keystore.so"

    private val abi: String =
        Build.SUPPORTED_ABIS?.firstOrNull() ?: DeviceProps.prop("ro.product.cpu.abi", "arm64-v8a")

    private val injectBin = File(moduleDir, "$abi/inject")
    private val libFile = File(moduleDir, "$abi/$libName")

    @Volatile private var running = false
    @Volatile private var lastPid = -1

    // The KeyMint HAL process (Android 12+). We inject the same lib with the same entry symbol; the
    // lib detects it is the HAL and installs only a read-only diagnostic (see keymint_entry.cpp).
    // Tracked separately from keystore2 so each is re-injected independently when its pid changes.
    private val halProcName = "android.hardware.security.keymint-service"
    @Volatile private var lastHalPid = -1

    // HAL-side hijack switch mirror. The HAL process (hal_keymint_default) cannot access() anything
    // under /data/adb (SELinux / KSU file label), so the probe reads persist.teesim.hal_hijack via
    // __system_property_get instead. This loop mirrors the optional convenience file
    // /data/adb/teesim/hal_hijack.enable into that property so `touch`/`rm` still works from a root
    // shell. Source of truth is the file; the property is the HAL-visible mirror (reset on each
    // daemon boot from the file, so persist.* not surviving a reboot is fine).
    private val halHijackFile = File(Const.DATA_DIR, "hal_hijack.enable")
    @Volatile private var lastHalHijackSynced: String? = null

    fun start() {
        if (running) return
        running = true
        if (!injectBin.exists() || !libFile.exists()) {
            SystemLogger.error(
                "Injector: missing artifacts (inject=${injectBin.exists()} lib=${libFile.exists()}) " +
                    "under ${moduleDir.absolutePath}/$abi"
            )
        }
        injectBin.setExecutable(true, false)
        Thread({ loop() }, "teesim-injector").apply {
            isDaemon = true
            start()
        }
    }

    private fun loop() {
        SystemLogger.info("Injector: watching $procName (abi=$abi lib=$libName)")
        var failures = 0
        while (running) {
            // Keep persist.teesim.hal_hijack in sync with the optional file switch so the HAL
            // process (which cannot read /data/adb) sees the user's toggle. Cheap when unchanged.
            syncHalHijackProp()
            // The full /proc walk in findPid touches every process's cmdline (~1000 reads on a
            // busy device); skip it while the pid we last injected is still alive, since it never
            // changes between keystore restarts. Fall back to the walk only once it's gone. The
            // fallback fires at most once per keystore restart (or per retry while injection keeps
            // failing), so log it; the common alive-pid path stays silent to keep the loop cheap.
            val pid =
                if (lastPid > 0 && isNamedProcess(lastPid, procName)) {
                    lastPid
                } else {
                    if (lastPid > 0) {
                        SystemLogger.debug(
                            "Injector: pid=$lastPid is no longer $procName; re-scanning /proc"
                        )
                    }
                    findPid(procName)
                }
            // Tell the log tail which process to capture, so the Logs panel shows the target
            // keystore's own output — even before we manage to inject it.
            LogTail.targetPid = if (pid > 0) pid else -1
            if (pid > 0 && pid != lastPid && serviceReady()) {
                if (inject(pid)) {
                    lastPid = pid
                    failures = 0
                    SystemLogger.info("Injector: injected into $procName pid=$pid")
                    confirmAsync(pid)
                } else {
                    failures++
                    SystemLogger.warning("Injector: injection into pid=$pid failed; will retry")
                }
            } else if (pid <= 0) {
                lastPid = -1 // process gone; force re-inject when it returns
            }
            // Also inject the KeyMint HAL process (Android 12+ only). This is additive and
            // independent of the keystore2 injection above; a failure here never affects keystore2.
            if (api >= 31) {
                val halPid =
                    if (lastHalPid > 0 && isNamedProcess(lastHalPid, halProcName)) {
                        lastHalPid
                    } else {
                        findPid(halProcName)
                    }
                if (halPid > 0 && halPid != lastHalPid) {
                    if (inject(halPid)) {
                        lastHalPid = halPid
                        SystemLogger.info("Injector: injected into $halProcName pid=$halPid")
                    } else {
                        SystemLogger.warning(
                            "Injector: injection into $halProcName pid=$halPid failed; will retry"
                        )
                    }
                } else if (halPid <= 0) {
                    if (lastHalPid > 0) {
                        SystemLogger.debug("Injector: $halProcName gone; will re-inject when it returns")
                    }
                    lastHalPid = -1
                }
            }

            // Back off when injection keeps failing so we don't hammer a wedged keystore.
            sleep(if (failures > 3) 10000 else 2000)
        }
    }

    /**
     * keystore forks before it registers its binder; wait for the service so we don't inject into a
     * half-initialised process.
     */
    private fun serviceReady(): Boolean {
        val name =
            if (api >= 31) "android.system.keystore2.IKeystoreService/default"
            else "android.security.keystore"
        return try {
            android.os.ServiceManager.getService(name) != null
        } catch (e: Throwable) {
            true // can't check (stub / older API): don't block injection
        }
    }

    /**
     * The control-channel hello is the real proof the lib loaded and bound the control socket. Warn
     * (don't re-inject — that risks double-hooking) if it never arrives.
     */
    private fun confirmAsync(pid: Int) {
        Thread(
                {
                    for (i in 0 until 24) { // ~12s
                        if (Control.libApi != 0) return@Thread
                        sleep(500)
                    }
                    SystemLogger.warning(
                        "Injector: injected pid=$pid but the lib never checked in over ${Const.CONTROL_SOCKET_PATH} " +
                            "(SELinux on the control socket? look for 'avc: denied' in logcat)"
                    )
                },
                "teesim-inject-confirm",
            )
            .apply {
                isDaemon = true
                start()
            }
    }

    private fun inject(pid: Int): Boolean {
        return try {
            val proc =
                ProcessBuilder(
                        injectBin.absolutePath,
                        pid.toString(),
                        libFile.absolutePath,
                        "entry",
                    )
                    .redirectErrorStream(true)
                    .start()
            val output = proc.inputStream.bufferedReader().readText()
            val code = proc.waitFor()
            if (code != 0) SystemLogger.warning("Injector: inject exit=$code output=$output")
            code == 0
        } catch (e: Exception) {
            SystemLogger.error("Injector: failed to run inject binary", e)
            false
        }
    }

    /** True if /proc/[pid]/cmdline's basename still matches [name], else false. */
    private fun isNamedProcess(pid: Int, name: String): Boolean {
        val cmd =
            try {
                File("/proc/$pid/cmdline").readBytes()
            } catch (e: Exception) {
                return false
            }
        if (cmd.isEmpty()) return false
        val end = cmd.indexOf(0.toByte()).let { if (it < 0) cmd.size else it }
        return String(cmd, 0, end).substringAfterLast('/') == name
    }

    /** Return the pid whose /proc/<pid>/cmdline basename matches [name], else -1. */
    private fun findPid(name: String): Int {
        val proc = File("/proc")
        val entries =
            proc.listFiles { f -> f.isDirectory && f.name.all { it.isDigit() } } ?: return -1
        for (dir in entries) {
            val cmdlineFile = File(dir, "cmdline")
            val cmd =
                try {
                    cmdlineFile.readBytes()
                } catch (e: Exception) {
                    continue
                }
            if (cmd.isEmpty()) continue
            val end = cmd.indexOf(0.toByte()).let { if (it < 0) cmd.size else it }
            val arg0 = String(cmd, 0, end)
            val base = arg0.substringAfterLast('/')
            if (base == name) return dir.name.toIntOrNull() ?: continue
        }
        return -1
    }

    /**
     * Mirror `/data/adb/teesim/hal_hijack.enable` existence into `persist.teesim.hal_hijack`
     * ("1"/"0") via [SysProp.set] (Magisk/KSU `resetprop -n`). Idempotent: only writes when the
     * desired value differs from what we last successfully synced, so the 2s inject loop does not
     * spam logs. Failure leaves [lastHalHijackSynced] untouched so the next tick retries.
     */
    private fun syncHalHijackProp() {
        val on = halHijackFile.exists()
        val value = if (on) "1" else "0"
        if (value == lastHalHijackSynced) return
        if (SysProp.set("persist.teesim.hal_hijack", value)) {
            lastHalHijackSynced = value
            SystemLogger.info(
                "Injector: synced persist.teesim.hal_hijack=$value " +
                    "(file ${if (on) "present" else "absent"})"
            )
        }
    }

    private fun sleep(ms: Long) {
        try {
            Thread.sleep(ms)
        } catch (ignored: InterruptedException) {}
    }
}
