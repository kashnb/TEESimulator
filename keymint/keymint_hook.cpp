// Interceptor that redirects keystore2's KeyMint transactions to our local
// binder.
//
// keystore2 resolves and caches the KeyMint proxy at boot, before we are
// injected, so we cannot redirect at resolution time. Instead we PLT-hook
// AIBinder_transact: for a transaction on the real KeyMint proxy whose code is
// one we handle, we copy the request into a parcel bound to our local binder and
// dispatch it there. The local binder itself decides, per request, whether to
// simulate or forward to the real HAL, so this hook is deliberately dumb.

#include <aidl/android/hardware/security/keymint/IKeyMintDevice.h>
#include <android/binder_ibinder.h>
#include <android/binder_parcel.h>
#include <android/binder_status.h>

#include <linux/android/binder.h>
#include <sys/syscall.h>
#include <cstdarg>
#include <sys/ioctl.h>
#include <sys/system_properties.h>
#include <time.h>
#include <unistd.h>

#include <atomic>
#include <cstdlib>
#include <cstring>
#include <map>
#include <mutex>
#include <set>
#include <string>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <vector>

// The subsystem every line from this file is stamped with; see injector/include/logging.hpp.
#define LOG_SUB "km/hook"
#include "keymint_hook.h"
#include "logging.hpp"
#include "lsplt.hpp"

using aidl::android::hardware::security::keymint::IKeyMintDevice;

// Implemented in keymint_router.cpp.
extern "C" AIBinder* teesim_router_new_device(int32_t security_level, AIBinder* real_binder);
// True if the calling uid belongs to a live target profile (keymint_router.cpp).
extern "C" bool teesim_is_target_uid(int32_t uid);
// RKP-only delete-intent tracking (keymint_router.cpp): is this prop one the user deleted, and note
// that we saw it live again so the daemon re-deletes it.
extern "C" bool teesim_rkp_is_delete_intent(const char* name);
extern "C" void teesim_rkp_note_reassert(const char* name);

namespace {

binder_status_t (*real_transact)(AIBinder*, transaction_code_t, AParcel**, AParcel**,
                                 binder_flags_t) = nullptr;

// Marks the current thread as forwarding into the real HAL, so we let those
// transactions pass straight through.
thread_local bool tls_forwarding = false;

std::mutex g_mu;
// Real KeyMint proxy -> our local device wrapping it. A nullptr value is a NEGATIVE cache ("do not
// wrap this proxy", i.e. a SOFTWARE-level km_compat device) so we neither re-probe its
// getHardwareInfo nor rebuild a device on every transact. Keyed on the raw proxy pointer, which is
// safe because keystore2 caches its per-level KeyMint devices for the process lifetime, so the
// pointer is stable and never reallocated (the negative cache relies on this too).
std::map<AIBinder*, AIBinder*> g_local_for_proxy;

// Our own local devices (the non-null values of g_local_for_proxy). IsKeyMintProxy matches any local
// IKeyMintDevice by descriptor, and our own TeesimKeyMintDevice is one, so IsKeyMintProxy excludes
// anything in this set. (Redirect dispatches our device through real_transact — the unhooked LSPlt
// backup — so it never re-enters the hook; forwarding recursion is prevented by tls_forwarding, not
// this set. This is a guard against any other caller transacting our device through the hooked symbol.)
//
// Guarded by a SEPARATE mutex, not g_mu: LocalFor holds g_mu across teesim_router_new_device, which
// makes a blocking getHardwareInfo IPC into the real HAL, while IsOurDevice runs on the transact hot
// path — one shared lock would stall every handled transact behind device construction. Lock order is
// always g_mu -> g_our_mu (IsOurDevice takes g_our_mu alone; LocalFor takes g_mu, then g_our_mu).
std::mutex g_our_mu;
std::set<AIBinder*> g_our_devices;

// True if `binder` is a TeesimKeyMintDevice we created.
bool IsOurDevice(AIBinder* binder) {
  std::lock_guard<std::mutex> lk(g_our_mu);
  return g_our_devices.count(binder) != 0;
}

bool IsHandled(transaction_code_t code) {
  switch (code) {
    case 3:   // generateKey
    case 4:   // importKey
    case 5:   // importWrappedKey
    case 6:   // upgradeKey
    case 7:   // deleteKey
    case 10:  // begin
    case 13:  // convertStorageKeyToEphemeral
    case 14:  // getKeyCharacteristics
      return true;
    default:
      return false;
  }
}

// Identity check for the KeyMint binder keystore2 transacts. We match on the class descriptor alone
// and do not require AIBinder_isRemote, so we catch KeyMint whether it is remote or in-process:
//
//   - Native KeyMint HAL: keystore2's TrustedEnvironment/StrongBox proxy is a remote binder.
//   - Legacy Keymaster (keymaster@4.x) backend: keystore2 has no native KeyMint, so per security level
//     it holds an in-process km_compat IKeyMintDevice (getKeyMintDevice) — stored directly (keymaster
//     4.0/4.1) or behind a BacklevelKeyMintWrapper (downlevel). Either way the binder that reaches
//     AIBinder_transact is a local proxy (isRemote==false).
//
// The SOFTWARE level is excluded by level, not here: keystore2 serves SecurityLevel::SOFTWARE from an
// in-process km_compat device on every device, and teesim_router_new_device returns nullptr for it
// (LocalFor caches that), so the software leg is never wrapped. See that function.
//
// The descriptor also matches our own local TeesimKeyMintDevice, so we exclude it (IsOurDevice). The
// descriptor is compared first, so the g_our_mu lookup runs only for actual IKeyMintDevice binders.
bool IsKeyMintProxy(AIBinder* binder) {
  const AIBinder_Class* clazz = AIBinder_getClass(binder);
  if (!clazz) return false;
  const char* desc = AIBinder_Class_getDescriptor(clazz);
  if (!desc || std::strcmp(desc, IKeyMintDevice::descriptor) != 0) return false;
  return !IsOurDevice(binder);
}

// What the RKP gate below decided on this thread, and for which uid. keystore2 resolves the
// remote-provisioning key on the app's own binder thread while it is still serving that app's
// generateKey, so the router can read this back and state, on the generateKey line itself, why the
// request did or did not arrive carrying a real attest key. "none" means the gate never ran on this
// thread — which is the answer whenever a request turns up with an attest key we never saw fetched.
thread_local const char* tls_rkp_verdict = "none";
thread_local int32_t tls_rkp_uid = -1;
// The request id the gate's own line carried, and when the verdict was recorded, so the router can
// say both which line this verdict came from and whether it is fresh enough to belong to the
// request in hand.
thread_local uint32_t tls_rkp_rid = 0;
thread_local uint64_t tls_rkp_at_ms = 0;

uint64_t NowMonoMs() {
  struct timespec ts{};
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return static_cast<uint64_t>(ts.tv_sec) * 1000u + static_cast<uint64_t>(ts.tv_nsec) / 1000000u;
}

// The framework RKP front-end keystore2 asks for a remote-provisioned attestation key. keystore2
// resolves it by calling IRemoteProvisioning.getRegistration on this binder; failing that transact
// makes keystore2 fall back to "no attest key" (get_attest_key_info -> Ok(None)) on a hybrid device,
// so it appends no real-hardware certificate chain to the key we mint.
bool IsRkpProvisioning(AIBinder* binder) {
  if (!AIBinder_isRemote(binder)) return false;
  const AIBinder_Class* clazz = AIBinder_getClass(binder);
  if (!clazz) return false;
  const char* desc = AIBinder_Class_getDescriptor(clazz);
  return desc && std::strcmp(desc, "android.security.rkp.IRemoteProvisioning") == 0;
}

// Read a security level's rkp_only property. Fills `raw` with the property's current value (empty
// string if unset) so our RKP-policy logging can report exactly what keystore2 and this guard see at
// decision time, and returns whether it is set to a truthy value ("true"/"1"). On such a level
// keystore2 has no batch key to fall back to, so denying its RKP lookup makes generateKey fail
// outright (get_attest_key_info returns Err instead of Ok(None)); there we must let the lookup
// through. We only ever READ the property — a global write would be an obvious detection point.
bool ReadRkpOnly(const char* name, char raw[PROP_VALUE_MAX]) {
  raw[0] = '\0';
  int n = __system_property_get(name, raw);
  return n > 0 && (std::strcmp(raw, "true") == 0 || std::strcmp(raw, "1") == 0);
}

// Log the device's remote-key-provisioning policy once, at install. These are the properties that
// decide whether our per-target RKP denial is safe: the two per-level rkp_only knobs keystore2 reads
// to pick its attestation-key source, plus enable_rkpd (whether the rkpd provisioner runs at all).
// Dumping the ground truth once makes every deny/NOT-denying decision below self-explanatory in a
// bug report — a reader can see what the guard is reacting to without guessing at the device state.
void LogRkpPolicySnapshot() {
  static const char* const kProps[] = {
      "remote_provisioning.tee.rkp_only",
      "remote_provisioning.strongbox.rkp_only",
      "persist.device_config.remote_key_provisioning_native.enable_rkpd",
  };
  for (const char* name : kProps) {
    char buf[PROP_VALUE_MAX] = {0};
    int n = __system_property_get(name, buf);
    LOGI("LogRkpPolicySnapshot: %s=%s", name, n > 0 ? buf : "<unset>");
  }
}

// Allocator for AParcel_readString: `length` includes the null terminator, or is -1 for a null string.
bool RkpStringAllocator(void* string_data, int32_t length, char** buffer) {
  char** out = static_cast<char**>(string_data);
  if (length < 0) {
    *out = nullptr;
    *buffer = nullptr;
    return true;
  }
  *out = static_cast<char*>(malloc(length));
  if (*out == nullptr) return false;
  *buffer = *out;
  return true;
}

// The instance part of an IRemotelyProvisionedComponent name. keystore2 asks for the
// interface-qualified instance its globals build for the security level —
// "android.hardware.security.keymint.IRemotelyProvisionedComponent/strongbox", never a bare
// "strongbox" — so the instance is whatever follows the last '/'.
const char* IrpcInstance(const char* name) {
  const char* slash = std::strrchr(name, '/');
  return slash ? slash + 1 : name;
}

// Which security level a getRegistration transact targets, read from its first argument — the
// IRemotelyProvisionedComponent name, whose instance is "strongbox" for StrongBox and "default" for
// TE. The interface header size is measured from a throwaway prepared transaction on the same binder,
// so no wire format is hardcoded; the input parcel's read position is saved and restored. `irpc_name`
// receives the name as read, so a bug report shows what the decision below was actually made on.
// Defaults to TE if unreadable.
bool GetRegIsStrongBox(AIBinder* binder, AParcel* in, std::string* irpc_name) {
  AParcel* probe = nullptr;
  if (AIBinder_prepareTransaction(binder, &probe) != STATUS_OK) return false;
  int32_t header = AParcel_getDataSize(probe);  // args begin past the interface header (cf. Redirect)
  AParcel_delete(probe);

  int32_t saved = AParcel_getDataPosition(in);
  if (AParcel_setDataPosition(in, header) != STATUS_OK) return false;
  char* name = nullptr;
  bool strongbox = false;
  if (AParcel_readString(in, &name, RkpStringAllocator) == STATUS_OK && name != nullptr) {
    strongbox = std::strcmp(IrpcInstance(name), "strongbox") == 0;
    irpc_name->assign(name);
  }
  free(name);
  AParcel_setDataPosition(in, saved);
  return strongbox;
}

// Return (creating if needed) the local device that wraps `proxy`.
AIBinder* LocalFor(AIBinder* proxy) {
  std::lock_guard<std::mutex> lk(g_mu);
  auto it = g_local_for_proxy.find(proxy);
  if (it != g_local_for_proxy.end()) return it->second;
  // teesim_router_new_device derives this proxy's real security level from the
  // wrapped HAL's getHardwareInfo(); the value passed here is only the fallback
  // used if that query fails.
  AIBinder* local = teesim_router_new_device(1 /* fallback: TRUSTED_ENVIRONMENT */, proxy);
  g_local_for_proxy[proxy] = local;  // may be nullptr (SOFTWARE): negative cache, do not re-probe
  if (local) {
    // Record our device so the relaxed IsKeyMintProxy never re-wraps it. We already hold g_mu; lock
    // order is g_mu -> g_our_mu. Never insert nullptr (a SOFTWARE proxy yields local==nullptr): the
    // "g_our_devices == our real devices" invariant must hold.
    std::lock_guard<std::mutex> lk(g_our_mu);
    g_our_devices.insert(local);
  }
  return local;
}

binder_status_t Redirect(AIBinder* local, transaction_code_t code, AParcel** in, AParcel** out,
                         binder_flags_t flags, AIBinder* proxy) {
  AParcel* my_in = nullptr;
  if (AIBinder_prepareTransaction(local, &my_in) != STATUS_OK) {
    return real_transact(proxy, code, in, out, flags);
  }
  int32_t hdr = AParcel_getDataSize(my_in);
  int32_t total = AParcel_getDataSize(*in);
  if (total < hdr || AParcel_appendFrom(*in, my_in, hdr, total - hdr) != STATUS_OK) {
    AParcel_delete(my_in);
    return real_transact(proxy, code, in, out, flags);
  }
  binder_status_t r = real_transact(local, code, &my_in, out, flags);  // consumes my_in
  AParcel_delete(*in);  // match AIBinder_transact's ownership contract
  *in = nullptr;
  return r;
}

binder_status_t HookedTransact(AIBinder* binder, transaction_code_t code, AParcel** in,
                               AParcel** out, binder_flags_t flags) {
  // TEESIM_AVD_DIAG: prove whether keystore2's KeyMint traffic reaches this PLT hook at all.
  // Logs the first N transactions with their interface descriptor, code and caller uid.
  // Remove once the Android 16 x86_64 path is confirmed.
  {
    static std::atomic<uint32_t> diag_calls{0};
    uint32_t diag_n = diag_calls.fetch_add(1, std::memory_order_relaxed);
    if (diag_n < 512) {
      const AIBinder_Class* diag_clazz = binder ? AIBinder_getClass(binder) : nullptr;
      const char* diag_desc = diag_clazz ? AIBinder_Class_getDescriptor(diag_clazz) : nullptr;
      LOGI("TEESIM_AVD_DIAG tx#%u code=%u desc=%s uid=%d keymint=%d", diag_n, code,
           diag_desc ? diag_desc : "(null)",
           static_cast<int>(AIBinder_getCallingUid()), IsKeyMintProxy(binder) ? 1 : 0);
    }
  }
  if (!tls_forwarding && in && *in) {
    // Deny a target app's remote-provisioning lookup so keystore2 attaches no real attest key. The
    // RKP resolution runs on this same binder thread (a current-thread tokio runtime block_on), while
    // keystore2 is still serving the app's generateKey, so getCallingUid is the app's uid. The gate is
    // per security level: keystore2 reads .tee.rkp_only for a TE request and .strongbox.rkp_only for a
    // StrongBox one, and denying an rkp-only level fails the key instead of falling back — so pick the
    // property matching this getRegistration's target (its irpcName) rather than the TEE one alone.
    if (IsRkpProvisioning(binder)) {
      int32_t uid = static_cast<int32_t>(AIBinder_getCallingUid());
      // The gate runs on the app's binder thread but outside any hooked entry point, so it stamps
      // its own context; the rid it records ties the verdict back to the line that made it.
      char rkp_ctx[64];
      tls_rkp_rid = teesim_log_new_rid();
      snprintf(rkp_ctx, sizeof(rkp_ctx), "[%d r%04x] ", uid, tls_rkp_rid);
      LogContext lc_(rkp_ctx);
      tls_rkp_uid = uid;
      tls_rkp_at_ms = NowMonoMs();
      if (!teesim_is_target_uid(uid)) {
        // Not a target *at this instant*: either the app really is out of scope, or the scope is
        // stale (a reinstall gave it a new uid and no re-resolve has run yet), or the lookup did not
        // arrive on the app's binder thread and this uid is not the app's at all. All three end the
        // same way — keystore2 gets a real, remotely provisioned attest key, and a leaf signed under
        // it keeps the REAL root of trust because we do not hold that key's private half. Say so
        // here; a silent allow is indistinguishable from never having been asked.
        tls_rkp_verdict = "allowed-not-target";
        LOGD("HookedTransact: RKP allowing IRemoteProvisioning transact code=%u for uid=%d (not a "
             "target uid at this moment; keystore2 may inject a real attest key we cannot re-root)",
             code, uid);
      } else {
        std::string irpc_name;
        bool strongbox = GetRegIsStrongBox(binder, *in, &irpc_name);
        const char* prop = strongbox ? "remote_provisioning.strongbox.rkp_only"
                                      : "remote_provisioning.tee.rkp_only";
        const char* level = strongbox ? "StrongBox" : "TEE";
        const char* irpc = irpc_name.empty() ? "<unreadable>" : irpc_name.c_str();
        char raw[PROP_VALUE_MAX] = {0};
        bool rkp_only = ReadRkpOnly(prop, raw);
        const char* val = raw[0] ? raw : "<unset>";
        if (rkp_only) {
          // The prop reads rkp_only=true. If the user deleted it, this is a reassertion (a vendor
          // .prop or a delayed config sync, #262) the daemon must undo — note it so the next
          // getUsage poll re-deletes it. We still ALLOW this one lookup: denying an rkp-only level
          // fails key generation outright (there is no batch fallback yet), which is worse than the
          // one leaked check this races with. Once the daemon re-deletes, the prop reads unset and
          // the ordinary deny -> keybox path takes over on the next provisioning.
          if (teesim_rkp_is_delete_intent(prop)) {
            teesim_rkp_note_reassert(prop);
            tls_rkp_verdict = "allowed-reasserted-pending-redelete";
            LOGW("HookedTransact: RKP lazy re-delete — %s reasserted to %s=%s for target uid=%d "
                 "despite a delete intent; allowing this lookup and asking the daemon to re-delete "
                 "(this check may leak once; the next one won't)",
                 level, prop, val, uid);
          } else {
            tls_rkp_verdict = "allowed-rkp-only-level";
            LOGI("HookedTransact: RKP NOT denying %s getRegistration for target uid=%d (irpcName=%s, "
                 "%s=%s; denial would fail key generation on an rkp-only level)",
                 level, uid, irpc, prop, val);
          }
        } else {
          tls_rkp_verdict = "denied";
          // The gate only knows what keystore2 will now do, not how the key will be rooted: a
          // patch-mode profile keeps real hardware with only its leaf re-signed.
          // DEBUG: the generateKey line that follows reports this verdict as rkp_gate=denied(...).
          LOGD("HookedTransact: RKP denying %s IRemoteProvisioning transact code=%u for target uid=%d "
               "(irpcName=%s, %s=%s; keystore2 will append no real attest-key chain)",
               level, code, uid, irpc, prop, val);
          AParcel_delete(*in);  // honour AIBinder_transact's ownership of the input parcel
          *in = nullptr;
          return STATUS_FAILED_TRANSACTION;  // -> Rust `?` -> get_attest_key_info Ok(None) on hybrid
        }
      }
    }
    if (IsHandled(code) && IsKeyMintProxy(binder)) {
      AIBinder* local = LocalFor(binder);
      if (local) return Redirect(local, code, in, out, flags, binder);
      // local == nullptr: a SOFTWARE-level proxy we deliberately do not wrap; fall through to
      // real_transact so keystore2's own software-key path runs untouched.
    }
  }
  return real_transact(binder, code, in, out, flags);
}

}  // namespace

extern "C" void teesim_hook_set_forwarding(bool forwarding) { tls_forwarding = forwarding; }

// The RKP gate's verdict for this thread, for the router to print on its generateKey line. Reading
// it clears it, so a later request that never reaches the gate reports "none" rather than inheriting
// the previous request's answer from the same binder thread. The age is what catches the case
// clearing cannot: a verdict armed for a request keystore2 then abandoned stays latched on the
// thread until something reads it, and only its age says it is not this request's.
extern "C" void teesim_hook_take_rkp_verdict(TsRkpVerdict* out) {
  if (!out) return;
  out->verdict = tls_rkp_verdict;
  out->uid = tls_rkp_uid;
  out->rid = tls_rkp_rid;
  out->age_ms = tls_rkp_at_ms != 0 ? static_cast<uint32_t>(NowMonoMs() - tls_rkp_at_ms) : 0;
  tls_rkp_verdict = "none";
  tls_rkp_uid = -1;
  tls_rkp_rid = 0;
  tls_rkp_at_ms = 0;
}

// Only hook real ELF modules: the main executable and shared libraries. Feeding
// LSPlt a non-ELF mapping (fonts, dex, oat, apk) makes its ELF parser fault.
bool IsHookableElf(const std::string& path, const std::string& exe) {
  if (path == exe) return true;
  if (path.size() < 3) return false;
  return path.compare(path.size() - 3, 3, ".so") == 0;
}


// TEESIM_AVD_DIAG: keystore2 on Android 16 is Rust and may drive binder through ioctl()
// directly, bypassing the AIBinder_transact PLT hook. Log outgoing BC_TRANSACTION codes
// (capped) so one CI run tells us which path the KeyMint calls really take.
static int (*g_real_ioctl)(int, unsigned long, void*) = nullptr;

// TEESIM_AVD_DIAG: extract the AIDL interface descriptor (length-prefixed UTF-16LE String16) from a
// transaction's request data and return it as UTF-8, reusing the same request data region that
// IsRkpDenyTransaction / DataHasInterface read. The interface token is a Parcel String16: a uint32
// length (char count, excluding NUL) followed by length+1 UTF-16LE code units, preceded by header
// words (strict-mode policy, optional work-source). We scan word-aligned for the first length word
// whose units are all printable ASCII and contain a '.', which uniquely picks out the reverse-DNS
// descriptor. Read-only; returns "?" when no token is found.
static std::string InterfaceName(const struct binder_transaction_data& tr) {
  if (tr.data.ptr.buffer == 0 || tr.data_size == 0 || tr.data_size >= (1u << 20)) return "?";
  const uint8_t* d = reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(tr.data.ptr.buffer));
  size_t scan = tr.data_size < 512 ? tr.data_size : 512;
  for (size_t i = 0; i + sizeof(uint32_t) <= scan; i += sizeof(uint32_t)) {
    uint32_t len = 0;
    std::memcpy(&len, d + i, sizeof(len));
    if (len == 0 || len > 128) continue;
    size_t bytes = static_cast<size_t>(len) * 2;
    if (i + sizeof(uint32_t) + bytes > scan) continue;
    const uint8_t* srep = d + i + sizeof(uint32_t);
    std::string out;
    bool ok = true, has_dot = false;
    for (uint32_t j = 0; j < len; ++j) {
      uint16_t ch = 0;
      std::memcpy(&ch, srep + j * 2, 2);
      if (ch < 0x20 || ch > 0x7e) { ok = false; break; }
      if (ch == static_cast<uint16_t>('.')) has_dot = true;
      out.push_back(static_cast<char>(ch));
    }
    if (ok && has_dot) return out;
  }
  return "?";
}

static void AvdDiagScanBinderWrite(const struct binder_write_read* bwr) {
  if (!bwr || bwr->write_size == 0 || bwr->write_buffer == 0) return;
  const uint8_t* buf = reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(bwr->write_buffer));
  size_t off = 0;
  while (off + sizeof(uint32_t) <= bwr->write_size) {
    uint32_t cmd = 0;
    memcpy(&cmd, buf + off, sizeof(cmd));
    off += sizeof(cmd);
    if (cmd == BC_TRANSACTION) {
      if (off + sizeof(struct binder_transaction_data) > bwr->write_size) return;
      struct binder_transaction_data tr;
      memcpy(&tr, buf + off, sizeof(tr));
      static std::atomic<uint32_t> n{0};
      uint32_t i = n.fetch_add(1, std::memory_order_relaxed);
      if (i < 256) {
        LOGI("TEESIM_AVD_DIAG ioctl BC_TRANSACTION#%u code=%u handle=%u ptr=%llx data=%llu", i,
             tr.code, tr.target.handle, static_cast<unsigned long long>(tr.target.ptr),
             static_cast<unsigned long long>(tr.data_size));
      }
      // Temporary diagnostic (pt24u): for each successfully parsed BC_TRANSACTION, log interface
      // descriptor, code, caller uid and target handle. Capped at 64 via its own counter; always on,
      // independent of the phase-2 switch. Pure read-only; changes no behaviour.
      {
        static std::atomic<int> dn{0};
        int di = dn.fetch_add(1, std::memory_order_relaxed);
        if (di < 64) {
          LOGI("TEESIM_AVD_DIAG tx: uid=%d handle=%u code=%u desc=%s",
               static_cast<int>(AIBinder_getCallingUid()), tr.target.handle, tr.code,
               InterfaceName(tr).c_str());
        }
      }
      off += sizeof(tr) + ((tr.data_size + 7u) & ~static_cast<size_t>(7u));
    } else if (cmd == BC_REPLY) {
      if (off + sizeof(struct binder_transaction_data) > bwr->write_size) return;
      struct binder_transaction_data tr;
      memcpy(&tr, buf + off, sizeof(tr));
      off += sizeof(tr) + ((tr.data_size + 7u) & ~static_cast<size_t>(7u));
    } else {
      return;
    }
  }
}

// =============================================================================
// A-plan: ioctl-level takeover of keystore2's KeyMint generateKey (code=3).
//
// keystore2's KeyMint traffic never reaches the AIBinder_transact PLT hook (keystore2 is Rust and
// drives binder through ioctl(BINDER_WRITE_READ) in libbinder-rs), so we intercept it one layer down,
// in HookedIoctl. The request bytes live out-of-line at tr.data.ptr.buffer; we rebuild them into an
// NDK AParcel with AParcel_create/AParcel_unmarshal (both weak-linked and resolved at runtime against
// keystore2's libbinder_ndk) and dispatch to a process-local TeesimKeyMintDevice, exactly like the
// transact-hook path does via Redirect -- no android::Parcel / libbinder dependency is introduced.
//
// Phase 1 (always on): when a target app's generateKey is seen we build the parcel, call the local TA
// read-only, and log `DIAG hijack: ...`. The transaction is NEVER modified; it always falls through to
// g_real_ioctl. Phase 2 (synthesising a BR_REPLY and suppressing the real call) is written below but
// gated behind the file switch /data/adb/teesim/ioctl_hijack.enable, which is absent by default, so
// flipping it on (then restarting keystore2) enables takeover with no rebuild. The iron rule holds
// throughout: any failure on any path forwards the ioctl unchanged.
// =============================================================================

// generateKey is FIRST_CALL_TRANSACTION + 2 == 3 for IKeyMintDevice (confirmed on-device).
static constexpr uint32_t kKeyMintGenerateKeyCode = 3;
// TRUSTED_ENVIRONMENT; the first-cut takeover treats every KeyMint handle as TEE (StrongBox is left
// alone -- see the handle gate below -- until a level cache exists).
static constexpr int32_t kSecurityLevelTee = 1;

// RemoteProvisioning interface keystore2 asks for an attest key through (same descriptor the
// transact-hook path's IsRkpProvisioning matches). Denying getRegistration makes keystore2 fall back
// to "no attest key", so our TA mints the chain from the keybox instead of appending a real one.
static constexpr const char* kRkpDescriptor = "android.security.rkp.IRemoteProvisioning";

// getRegistration is also issued by system processes during keystore init; killing those would break
// boot. So the RKP denial fires only for these scope uids (in ADDITION to the teesim_is_target_uid
// gate), matching the profile scope.
static bool IsRkpScopeUid(int32_t uid) {
  switch (uid) {
    case 10144:
    case 10147:
    case 10218:
    case 10221:
      return true;
    default:
      return false;
  }
}

// Serialises the phase-2 write-buffer rewrite (keystore2 is multi-threaded; ioctl frequency is low).
static std::mutex g_ioctl_mu;

// handle -> is this a KeyMint binder. Populated by matching the AIDL interface token in the request
// data against IKeyMintDevice::descriptor, so no handle is hardcoded (observed: 5/6 carry KeyMint, 1
// is servicemanager).
static std::mutex g_km_mu;
static std::unordered_map<uint32_t, bool> g_km_handles;

// Reply buffers we malloc'd and handed to the client inside a synthesised BR_REPLY. The client frees
// them with BC_FREE_BUFFER, whose pointer the kernel would reject (EINVAL) -- so we intercept those
// frees and release the memory ourselves.
static std::mutex g_synth_mu;
static std::unordered_set<uintptr_t> g_synth_bufs;

// The process-local TEE device, built once (teesim_router_new_device runs a blocking getHardwareInfo
// only when wrapping a real binder; here real=nullptr so it just makes a GENERATE-mode device).
static AIBinder* g_local_tee = nullptr;
static std::once_flag g_local_tee_once;
static AIBinder* GetLocalTee() {
  std::call_once(g_local_tee_once,
                 [] { g_local_tee = teesim_router_new_device(kSecurityLevelTee, nullptr); });
  return g_local_tee;
}

// Phase-2 master switch. Cached: toggling it takes effect on the next keystore2 start, like the spec.
static bool HijackEnabled() {
  static std::atomic<int> cached{-1};
  int c = cached.load(std::memory_order_relaxed);
  if (c < 0) {
    c = access("/data/adb/teesim/ioctl_hijack.enable", F_OK) == 0 ? 1 : 0;
    cached.store(c, std::memory_order_relaxed);
  }
  return c == 1;
}

// True if the first <=512 bytes of a request's data region contain the UTF-16 (little-endian) encoding
// of IKeyMintDevice::descriptor. We search rather than assume a fixed offset, so a work-source or
// other interface-header prefix ahead of the token does not defeat the match.
static bool DataHasInterface(const uint8_t* data, size_t len, const char* desc) {
  const size_t dlen = desc ? std::strlen(desc) : 0;
  if (dlen == 0) return false;
  size_t scan = len < 512 ? len : 512;
  if (scan < dlen * 2) return false;
  for (size_t i = 0; i + dlen * 2 <= scan; i += 2) {
    bool ok = true;
    for (size_t j = 0; j < dlen; ++j) {
      uint16_t ch = 0;
      std::memcpy(&ch, data + i + j * 2, 2);
      if (ch != static_cast<uint16_t>(static_cast<unsigned char>(desc[j]))) { ok = false; break; }
    }
    if (ok) return true;
  }
  return false;
}

static bool DataHasKeyMintInterface(const uint8_t* data, size_t len) {
  return DataHasInterface(data, len, IKeyMintDevice::descriptor);
}

static bool IsKnownKeyMintHandle(uint32_t handle) {
  std::lock_guard<std::mutex> lk(g_km_mu);
  auto it = g_km_handles.find(handle);
  return it != g_km_handles.end() && it->second;
}

// Validity gate for a transaction's data region before we dereference tr.data.ptr.buffer.
static bool DataRegionSane(const struct binder_transaction_data& tr) {
  return tr.data.ptr.buffer != 0 && tr.data_size > 0 && tr.data_size < (1u << 20);
}

// True if this transaction is an RKP getRegistration we should deny: it carries the RemoteProvisioning
// interface token, is not one-way, and the caller is both a target uid and in the hardcoded RKP scope
// set. Reads only the request data; no side effects.
static bool IsRkpDenyTransaction(const struct binder_transaction_data& tr) {
  if (tr.flags & TF_ONE_WAY) return false;
  if (!DataRegionSane(tr)) return false;
  const uint8_t* d = reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(tr.data.ptr.buffer));
  if (!DataHasInterface(d, tr.data_size, kRkpDescriptor)) return false;
  const int32_t uid = static_cast<int32_t>(AIBinder_getCallingUid());
  return IsRkpScopeUid(uid) && teesim_is_target_uid(uid);
}

// Build an NDK AParcel bound to `local` holding the raw request bytes, dispatch generateKey to the
// local TA through the unhooked AIBinder_transact backup, and return its reply parcel in *out (caller
// deletes it). Returns STATUS_OK only when *out is set. The input parcel is consumed by the transact.
static binder_status_t CallLocalGenerateKey(AIBinder* local, const struct binder_transaction_data& tr,
                                            AParcel** out) {
  *out = nullptr;
  if (!real_transact) return STATUS_FAILED_TRANSACTION;  // no unhooked path to dispatch on
  AParcel* in = nullptr;
  // prepareTransaction yields an AParcel already associated with `local` (AIBinder_transact rejects a
  // parcel bound to any other binder); unmarshal then replaces its data wholesale with the raw request
  // bytes, leaving that association intact.
  if (AIBinder_prepareTransaction(local, &in) != STATUS_OK || in == nullptr) {
    return STATUS_FAILED_TRANSACTION;
  }
  const uint8_t* raw = reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(tr.data.ptr.buffer));
  if (AParcel_unmarshal(in, raw, tr.data_size) != STATUS_OK) {
    AParcel_delete(in);
    return STATUS_FAILED_TRANSACTION;
  }
  // The cast assumption underlying the whole scheme: the reconstructed parcel must be exactly the
  // request size. If not, bail and let keystore2's real path run.
  if (AParcel_getDataSize(in) != static_cast<int32_t>(tr.data_size)) {
    AParcel_delete(in);
    return STATUS_BAD_VALUE;
  }
  AParcel_setDataPosition(in, 0);
  // Dispatch on the local device via the unhooked transact backup (as Redirect does), code=3, no
  // oneway. real_transact consumes `in`.
  return real_transact(local, kKeyMintGenerateKeyCode, &in, out, 0);
}

// Phase-1 read-only probe: prove the local TA answers this app's generateKey and emit one DIAG line.
// Never alters the transaction.
static void DiagProbeGenerateKey(const struct binder_transaction_data& tr) {
  AIBinder* local = GetLocalTee();
  const int uid = static_cast<int>(AIBinder_getCallingUid());
  if (!local) {
    LOGI("DIAG hijack: uid=%d handle=%u code=%u in=%d out=%d certs=%d (no local TEE device)", uid,
         tr.target.handle, tr.code, static_cast<int>(tr.data_size), -1, -1);
    return;
  }
  AParcel* out = nullptr;
  binder_status_t st = CallLocalGenerateKey(local, tr, &out);
  const int out_len = (st == STATUS_OK && out) ? AParcel_getDataSize(out) : -1;
  // certs: parsing KeyCreationResult's chain out of the reply parcel is deferred; -1 == not parsed.
  LOGI("DIAG hijack: uid=%d handle=%u code=%u in=%d out=%d certs=%d st=%d", uid, tr.target.handle,
       tr.code, static_cast<int>(tr.data_size), out_len, -1, static_cast<int>(st));
  if (out) AParcel_delete(out);
}

// One decoded command from a BINDER_WRITE_READ write buffer.
struct WbCmd {
  uint32_t cmd = 0;
  size_t off = 0;        // offset of the command word within the write buffer
  size_t len = 0;        // total bytes this command occupies (word + payload)
  bool has_tr = false;   // BC_TRANSACTION / BC_REPLY payload present
  struct binder_transaction_data tr {};
  uintptr_t free_ptr = 0;  // BC_FREE_BUFFER argument
};

// Decode every command in a write buffer. Returns false (and leaves `out` partial) the moment an
// unrecognised or truncated command is hit -- the caller then forwards unchanged, never guessing.
// NOTE: in the command stream a BC_TRANSACTION is followed only by binder_transaction_data; the data
// region is out-of-line at tr.data.ptr.buffer, so a command's length never includes tr.data_size.
static bool DecodeWriteBuffer(const uint8_t* buf, size_t size, std::vector<WbCmd>* out) {
  size_t off = 0;
  while (off + sizeof(uint32_t) <= size) {
    WbCmd c;
    c.off = off;
    std::memcpy(&c.cmd, buf + off, sizeof(uint32_t));
    size_t p = off + sizeof(uint32_t);
    if (c.cmd == BC_TRANSACTION || c.cmd == BC_REPLY) {
      if (p + sizeof(struct binder_transaction_data) > size) return false;
      std::memcpy(&c.tr, buf + p, sizeof(c.tr));
      c.has_tr = true;
      c.len = sizeof(uint32_t) + sizeof(struct binder_transaction_data);
    } else if (c.cmd == BC_FREE_BUFFER) {
      if (p + sizeof(binder_uintptr_t) > size) return false;
      std::memcpy(&c.free_ptr, buf + p, sizeof(binder_uintptr_t));
      c.len = sizeof(uint32_t) + sizeof(binder_uintptr_t);
    } else {
      return false;  // unknown command: stop, do not guess payload length
    }
    out->push_back(c);
    off += c.len;
  }
  return off == size;  // whole buffer accounted for, cleanly
}

// Learn KeyMint handles from this write buffer and, when probing, run the phase-1 DIAG for each
// target-app generateKey. Read-only; never touches the buffer.
static void ScanKeyMintCache(const struct binder_write_read* bwr, bool do_probe) {
  if (!bwr || bwr->write_buffer == 0 || bwr->write_size == 0) return;
  const uint8_t* buf = reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(bwr->write_buffer));
  std::vector<WbCmd> cmds;
  DecodeWriteBuffer(buf, bwr->write_size, &cmds);  // partial decode is fine for a read-only scan
  for (const auto& c : cmds) {
    if (c.cmd != BC_TRANSACTION || !c.has_tr) continue;
    if (DataRegionSane(c.tr)) {
      const uint8_t* d = reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(c.tr.data.ptr.buffer));
      if (DataHasKeyMintInterface(d, c.tr.data_size)) {
        std::lock_guard<std::mutex> lk(g_km_mu);
        g_km_handles[c.tr.target.handle] = true;
      }
    }
    if (!do_probe) continue;
    // RKP getRegistration (phase 1, switch off): it WOULD be denied in phase 2; log only, never modify.
    if (IsRkpDenyTransaction(c.tr)) {
      LOGI("DIAG hijack: rkp getRegistration seen (switch off) uid=%d code=%u handle=%u",
           static_cast<int>(AIBinder_getCallingUid()), c.tr.code, c.tr.target.handle);
      continue;
    }
    if (c.tr.code != kKeyMintGenerateKeyCode || (c.tr.flags & TF_ONE_WAY)) continue;
    if (!IsKnownKeyMintHandle(c.tr.target.handle)) continue;
    if (!teesim_is_target_uid(static_cast<int32_t>(AIBinder_getCallingUid()))) continue;
    if (!DataRegionSane(c.tr)) continue;
    DiagProbeGenerateKey(c.tr);
  }
}

// Phase-2 outcome.
enum class HijackResult {
  kForwardUnchanged,  // leave bwr as-is, call the kernel
  kForwardModified,   // bwr->write_size was shrunk (our BC_FREE_BUFFERs excised), call the kernel
  kSuppress,          // reply synthesised; do NOT call the kernel
};

// Rebuild the write buffer keeping only the commands at the given indices, compacting in place, and
// update write_size / write_consumed to match.
static void RewriteWriteBuffer(struct binder_write_read* bwr, const std::vector<WbCmd>& cmds,
                               const std::vector<size_t>& keep) {
  uint8_t* buf = reinterpret_cast<uint8_t*>(static_cast<uintptr_t>(bwr->write_buffer));
  size_t w = 0;
  for (size_t idx : keep) {
    const WbCmd& c = cmds[idx];
    if (w != c.off) std::memmove(buf + w, buf + c.off, c.len);
    w += c.len;
  }
  bwr->write_size = w;
  bwr->write_consumed = w;
}

// Build the GENERATE reply: dispatch the request to the local TA and marshal its reply parcel into a
// freshly malloc'd buffer (caller owns it). Returns false on any failure.
static bool BuildGenerateReply(const struct binder_transaction_data& tr, void** reply_out,
                               int32_t* len_out) {
  *reply_out = nullptr;
  *len_out = 0;
  AIBinder* local = GetLocalTee();
  if (!local) return false;
  AParcel* out = nullptr;
  if (CallLocalGenerateKey(local, tr, &out) != STATUS_OK || out == nullptr) {
    if (out) AParcel_delete(out);
    return false;
  }
  int32_t n = AParcel_getDataSize(out);
  if (n < 0) { AParcel_delete(out); return false; }
  void* buf = std::malloc(n > 0 ? static_cast<size_t>(n) : 1);
  bool ok = buf != nullptr &&
            (n == 0 || AParcel_marshal(out, static_cast<uint8_t*>(buf), 0,
                                       static_cast<size_t>(n)) == STATUS_OK);
  AParcel_delete(out);
  if (!ok) { std::free(buf); return false; }
  *reply_out = buf;
  *len_out = n;
  return true;
}

// Build the RKP-denial reply: an AIDL failure status header (EX_UNSUPPORTED_OPERATION + "rkp denied")
// marshalled into a freshly malloc'd buffer (caller owns it). We use the NDK's own status writer
// (AStatus_* + AParcel_writeStatusHeader) so the on-wire bytes are exactly what keystore2's binder-rs
// client parses for a failed transact: int32 exception code (-7) followed by a String16 message. For a
// non-EX_NONE status no return values follow, which is correct for a denied getRegistration.
static bool BuildRkpDenyReply(void** reply_out, int32_t* len_out) {
  *reply_out = nullptr;
  *len_out = 0;
  AStatus* st = AStatus_fromExceptionCodeWithMessage(EX_UNSUPPORTED_OPERATION, "rkp denied");
  if (!st) return false;
  AParcel* p = AParcel_create();
  if (!p) { AStatus_delete(st); return false; }
  binder_status_t ws = AParcel_writeStatusHeader(p, st);
  AStatus_delete(st);
  if (ws != STATUS_OK) { AParcel_delete(p); return false; }
  int32_t n = AParcel_getDataSize(p);
  if (n < 0) { AParcel_delete(p); return false; }
  void* buf = std::malloc(n > 0 ? static_cast<size_t>(n) : 1);
  bool ok = buf != nullptr &&
            (n == 0 || AParcel_marshal(p, static_cast<uint8_t*>(buf), 0,
                                       static_cast<size_t>(n)) == STATUS_OK);
  AParcel_delete(p);
  if (!ok) { std::free(buf); return false; }
  *reply_out = buf;
  *len_out = n;
  return true;
}

// Compose a synthesised BR_REPLY into the read buffer carrying `reply`/`out_len` (an out-of-line
// malloc'd buffer we own, already registered in g_synth_bufs), swallow the client's stale free-buffers,
// and mark the whole write consumed. The read buffer only needs the command header: the reply data is
// out-of-line, referenced by the pointer below, exactly as the kernel delivers a real reply.
static void EmitSynthReply(struct binder_write_read* bwr, void* reply, int32_t out_len,
                           uint32_t sender_euid, const std::vector<uintptr_t>& our_frees) {
  uint8_t* rb = reinterpret_cast<uint8_t*>(static_cast<uintptr_t>(bwr->read_buffer));
  uint32_t br = BR_REPLY;
  std::memcpy(rb, &br, sizeof(br));
  struct binder_transaction_data rep;
  std::memset(&rep, 0, sizeof(rep));
  rep.code = 0;      // BR_REPLY carries no method code
  rep.flags = 0;     // not oneway, no fds
  rep.sender_euid = sender_euid;  // preserve the caller's identity
  rep.data_size = out_len;
  rep.offsets_size = 0;
  rep.data.ptr.buffer = static_cast<binder_uintptr_t>(reinterpret_cast<uintptr_t>(reply));
  rep.data.ptr.offsets = 0;
  std::memcpy(rb + sizeof(uint32_t), &rep, sizeof(rep));
  bwr->read_consumed = sizeof(uint32_t) + sizeof(struct binder_transaction_data);
  for (uintptr_t p : our_frees) {
    std::lock_guard<std::mutex> lk(g_synth_mu);
    if (g_synth_bufs.erase(p)) std::free(reinterpret_cast<void*>(p));
  }
  bwr->write_consumed = bwr->write_size;  // we consumed the whole write
}

// What kind of takeover a transaction qualifies for.
enum class HijackKind { kNone, kGenerateKey, kRkpDeny };

// True if this transaction is a target-app KeyMint generateKey we should take over.
static bool IsGenerateKeyHijack(const struct binder_transaction_data& tr) {
  return !(tr.flags & TF_ONE_WAY) && DataRegionSane(tr) && tr.code == kKeyMintGenerateKeyCode &&
         IsKnownKeyMintHandle(tr.target.handle) &&
         teesim_is_target_uid(static_cast<int32_t>(AIBinder_getCallingUid()));
}

// Attempt phase-2 takeover. Caller holds g_ioctl_mu. Safe-by-construction: we only suppress when the
// write buffer is nothing but (optionally) our own BC_FREE_BUFFERs plus exactly one transaction we take
// over -- a target-app generateKey (reply = TA result) or an RKP getRegistration (reply = AIDL failure)
// -- whose reply we can synthesise into the read buffer; any other shape either just excises our stale
// free-buffers (so the kernel never sees a pointer it rejects) or is forwarded untouched.
static HijackResult TryHijack(struct binder_write_read* bwr) {
  if (!bwr || bwr->write_buffer == 0 || bwr->write_size == 0) return HijackResult::kForwardUnchanged;
  const uint8_t* buf = reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(bwr->write_buffer));
  std::vector<WbCmd> cmds;
  if (!DecodeWriteBuffer(buf, bwr->write_size, &cmds) || cmds.empty()) {
    return HijackResult::kForwardUnchanged;  // unparseable -> never meddle
  }

  std::vector<uintptr_t> our_frees;
  std::vector<size_t> keep;  // indices to retain if we end up only excising frees
  int hj_idx = -1;
  HijackKind hj_kind = HijackKind::kNone;
  int other_cmds = 0;  // non-free, non-the-one-hijacked commands

  for (size_t i = 0; i < cmds.size(); ++i) {
    const WbCmd& c = cmds[i];
    if (c.cmd == BC_FREE_BUFFER) {
      bool ours;
      { std::lock_guard<std::mutex> lk(g_synth_mu); ours = g_synth_bufs.count(c.free_ptr) != 0; }
      if (ours) { our_frees.push_back(c.free_ptr); continue; }  // excise ours
      keep.push_back(i);  // a real free: must reach the kernel
      ++other_cmds;
      continue;
    }
    if (c.cmd == BC_TRANSACTION && c.has_tr && hj_idx < 0) {
      if (IsGenerateKeyHijack(c.tr)) {
        hj_idx = static_cast<int>(i);
        hj_kind = HijackKind::kGenerateKey;
        continue;  // takeover candidate; not kept and not counted as "other"
      }
      if (IsRkpDenyTransaction(c.tr)) {
        hj_idx = static_cast<int>(i);
        hj_kind = HijackKind::kRkpDeny;
        continue;
      }
    }
    keep.push_back(i);
    ++other_cmds;
  }

  // We can only synthesise a reply when nothing else needs the kernel this round (writing BR_REPLY and
  // then letting the kernel run would clobber our read buffer). Otherwise fall back to excision/forward
  // so the real transaction still runs -- safe, just not taken over this time.
  const size_t reply_hdr = sizeof(uint32_t) + sizeof(struct binder_transaction_data);
  if (hj_idx >= 0 && other_cmds == 0 && bwr->read_buffer != 0 && bwr->read_size >= reply_hdr) {
    const struct binder_transaction_data& tr = cmds[hj_idx].tr;
    void* reply = nullptr;
    int32_t out_len = 0;
    const bool built = (hj_kind == HijackKind::kGenerateKey)
                           ? BuildGenerateReply(tr, &reply, &out_len)
                           : BuildRkpDenyReply(&reply, &out_len);
    if (built) {
      { std::lock_guard<std::mutex> lk(g_synth_mu); g_synth_bufs.insert(reinterpret_cast<uintptr_t>(reply)); }
      EmitSynthReply(bwr, reply, out_len, tr.sender_euid, our_frees);
      const int uid = static_cast<int>(AIBinder_getCallingUid());
      if (hj_kind == HijackKind::kGenerateKey) {
        LOGI("TEESIM_AVD_DIAG ioctl hijack: suppressed generateKey uid=%d handle=%u out=%d", uid,
             tr.target.handle, out_len);
      } else {
        LOGI("DIAG hijack: rkp getRegistration denied uid=%d code=%u handle=%u", uid, tr.code,
             tr.target.handle);
        LOGI("TEESIM_AVD_DIAG ioctl hijack: suppressed rkp uid=%d code=%u handle=%u out=%d", uid,
             tr.code, tr.target.handle, out_len);
      }
      return HijackResult::kSuppress;
    }
  }
  // Not suppressed (we returned above on success): any transaction we identified must still reach its
  // real service, so keep it in the forwarded stream rather than dropping it.
  if (hj_idx >= 0) {
    keep.push_back(static_cast<size_t>(hj_idx));
    std::sort(keep.begin(), keep.end());
  }

  // No suppression. If we identified any of our own BC_FREE_BUFFERs, excise them (the kernel would
  // reject their pointers); otherwise forward byte-for-byte.
  if (!our_frees.empty()) {
    RewriteWriteBuffer(bwr, cmds, keep);
    for (uintptr_t p : our_frees) {
      std::lock_guard<std::mutex> lk(g_synth_mu);
      if (g_synth_bufs.erase(p)) std::free(reinterpret_cast<void*>(p));
    }
    return HijackResult::kForwardModified;
  }
  return HijackResult::kForwardUnchanged;
}
static int HookedIoctl(int fd, unsigned long req, void* arg) {
  {
    static std::atomic<uint32_t> n{0};
    uint32_t i = n.fetch_add(1, std::memory_order_relaxed);
    if (i < 32) LOGI("TEESIM_AVD_DIAG ioctl-call#%u fd=%d req=%#lx", i, fd, req);
  }
  if (req == BINDER_WRITE_READ && arg != nullptr) {
    auto* bwr = static_cast<struct binder_write_read*>(arg);
    AvdDiagScanBinderWrite(bwr);  // keep the original BC_TRANSACTION trace intact
    const bool hijack = HijackEnabled();
    // Phase 1 (read-only): learn KeyMint handles and, when takeover is OFF, probe each generateKey.
    ScanKeyMintCache(bwr, /*do_probe=*/!hijack);
    // Phase 2 (gated OFF by default): take over generateKey at the ioctl layer.
    if (hijack) {
      std::lock_guard<std::mutex> lk(g_ioctl_mu);
      switch (TryHijack(bwr)) {
        case HijackResult::kSuppress:
          return 0;  // reply already written into the read buffer; do not touch the kernel
        case HijackResult::kForwardModified:
        case HijackResult::kForwardUnchanged:
          break;  // fall through to the real ioctl with (possibly) a shrunk write buffer
      }
    }
  }
  return g_real_ioctl ? g_real_ioctl(fd, req, arg) : -1;
}


// TEESIM_AVD_DIAG: heartbeat for the ioctl hook (is it called at all?) and a syscall() hook,
// because binder-rs may issue SYS_ioctl directly instead of calling libc's ioctl wrapper.
static long (*g_real_syscall)(long, ...) = nullptr;

static long HookedSyscall(long number, ...) {
  va_list ap;
  va_start(ap, number);
  long a1 = va_arg(ap, long);
  long a2 = va_arg(ap, long);
  long a3 = va_arg(ap, long);
  long a4 = va_arg(ap, long);
  long a5 = va_arg(ap, long);
  long a6 = va_arg(ap, long);
  va_end(ap);
  if (number == SYS_ioctl) {
    static std::atomic<uint32_t> n{0};
    uint32_t i = n.fetch_add(1, std::memory_order_relaxed);
    if (i < 32) {
      LOGI("TEESIM_AVD_DIAG syscall SYS_ioctl#%u fd=%ld req=%#lx", i, a1,
           static_cast<unsigned long>(a2));
    }
    if (static_cast<unsigned long>(a2) == BINDER_WRITE_READ && a3 != 0) {
      AvdDiagScanBinderWrite(reinterpret_cast<const struct binder_write_read*>(
          static_cast<uintptr_t>(a3)));
    }
  }
  return g_real_syscall ? g_real_syscall(number, a1, a2, a3, a4, a5, a6) : -1;
}

extern "C" bool teesim_hook_install() {
  LogRkpPolicySnapshot();  // one-shot ground truth for the RKP-denial decisions HookedTransact makes
  char exe_buf[512] = {0};
  ssize_t n = readlink("/proc/self/exe", exe_buf, sizeof(exe_buf) - 1);
  std::string exe = n > 0 ? std::string(exe_buf, n) : std::string();

  const auto maps = lsplt::MapInfo::Scan();

  // Register the AIBinder_transact hook across a chosen set of modules and commit. `exe_only`
  // limits it to the main executable; otherwise every ELF module (main exe + .so) is probed.
  auto register_and_commit = [&](bool exe_only) {
    std::set<std::pair<dev_t, ino_t>> seen;
    for (const auto& m : maps) {
      if (m.path.empty() || m.inode == 0) continue;
      if (exe_only ? (m.path != exe) : !IsHookableElf(m.path, exe)) continue;
      if (!seen.insert({m.dev, m.inode}).second) continue;
      bool diag_ok_tx = lsplt::RegisterHook(m.dev, m.inode, "AIBinder_transact",
                          reinterpret_cast<void*>(HookedTransact),
                          reinterpret_cast<void**>(&real_transact));
      // TEESIM_AVD_DIAG: also hook ioctl so binder-rs traffic (if any) is visible.
      bool diag_ok_io = lsplt::RegisterHook(m.dev, m.inode, "ioctl",
                          reinterpret_cast<void*>(HookedIoctl),
                          reinterpret_cast<void**>(&g_real_ioctl));
      bool diag_ok_sc = lsplt::RegisterHook(m.dev, m.inode, "syscall",
                          reinterpret_cast<void*>(HookedSyscall),
                          reinterpret_cast<void**>(&g_real_syscall));
      LOGI("TEESIM_AVD_DIAG install: %s reg_tx=%d reg_ioctl=%d reg_syscall=%d",
           m.path.c_str(), diag_ok_tx ? 1 : 0, diag_ok_io ? 1 : 0, diag_ok_sc ? 1 : 0);
    }
    // CommitHook returns false when a probed module doesn't import the symbol, which is
    // expected; success is that the caller's slot was patched (backup set).
    lsplt::CommitHook();
    LOGI("TEESIM_AVD_DIAG commit: real_tx=%p real_ioctl=%p real_syscall=%p",
         reinterpret_cast<void*>(real_transact), reinterpret_cast<void*>(g_real_ioctl),
         reinterpret_cast<void*>(g_real_syscall));
  };

  // The transaction we intercept — keystore2 forwarding to the real KeyMint — is issued from
  // the main executable, which is where AIBinder_transact is imported (keystore2's binder client
  // is linked into the binary). So probe just the executable's PLT first: this avoids scanning
  // (and having LSPlt warn about) every unrelated .so. Only if the importer isn't the executable
  // on some build do we widen to a full ELF scan, so coverage is never lost.
  if (!exe.empty()) {
    register_and_commit(/*exe_only=*/true);
    if (real_transact != nullptr) {
      LOGI("teesim_hook_install: AIBinder_transact patched in the main executable (%s)", exe.c_str());
      return true;
    }
  }
  register_and_commit(/*exe_only=*/false);
  LOGI("teesim_hook_install: AIBinder_transact %s after full ELF scan",
       real_transact != nullptr ? "patched" : "not found (no importer)");
  return real_transact != nullptr;
}
