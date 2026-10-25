// Injection entry point for the KeyMint interceptor (Android 12+).
//
// The daemon injects this library into keystore2 AND into the KeyMint HAL process
// (android.hardware.security.keymint-service), always with the same entry symbol. We branch on the
// injected process:
//   * keystore2  -> install the AIBinder_transact / ioctl interceptor and start the control server;
//                   the daemon connects and pushes the resolved profile set. (Unchanged behaviour.)
//   * KeyMint HAL -> install ONLY a read-only ioctl diagnostic (hal-tx trace). No control server, no
//                   interceptor, no behaviour change. This is the first, independently verifiable step
//                   toward moving the server-side takeover into the HAL process.
// Nothing is read from disk for config here -- the lib is a pure engine driven by control pushes.

#include <fcntl.h>
#include <unistd.h>
#include <cstring>
#include <thread>

#include "control.h"
// The subsystem every line from this file is stamped with; see injector/include/logging.hpp.
#define LOG_SUB "km"
#include "logging.hpp"

// keymint_hook.cpp
extern "C" bool teesim_hook_install();      // keystore2 interceptor (full)
extern "C" bool teesim_hook_install_hal();  // HAL-process read-only diagnostic
// keymint_hook.cpp: gated (hal_hijack.enable) route-A addService-override feasibility probe.
extern "C" void teesim_hal_takeover_probe();

// True when this process is the KeyMint HAL (basename of /proc/self/cmdline arg0 contains
// "keymint-service"), matching both the C++ and Rust default-HAL binary names.
static bool teesim_in_keymint_hal() {
  char buf[256] = {0};
  int fd = open("/proc/self/cmdline", O_RDONLY | O_CLOEXEC);
  if (fd < 0) return false;
  ssize_t n = read(fd, buf, sizeof(buf) - 1);
  close(fd);
  if (n <= 0) return false;
  buf[n < static_cast<ssize_t>(sizeof(buf)) ? n : static_cast<ssize_t>(sizeof(buf)) - 1] = '\0';
  const char* arg0 = buf;                      // arg0 is NUL-terminated within the buffer
  const char* slash = std::strrchr(arg0, '/');
  const char* base = slash ? slash + 1 : arg0;
  return std::strstr(base, "keymint-service") != nullptr;
}

extern "C" [[gnu::visibility("default")]] bool entry(void* /*handle*/) {
  if (teesim_in_keymint_hal()) {
    LOGI("entry: KeyMint HAL diagnostic mode (read-only hal-tx trace)");
    bool ok = teesim_hook_install_hal();
    LOGI("entry: HAL ioctl hook installed=%d", ok);
    // Route-A groundwork (gated behind /data/adb/teesim/hal_hijack.enable, default OFF): probe
    // addService-override feasibility on a DETACHED thread so AServiceManager_waitForService never
    // blocks the HAL's own service registration and entry() returns immediately. Switch-off and any
    // failure leave the real HAL untouched (IRON RULE).
    std::thread(teesim_hal_takeover_probe).detach();
    return ok;
  }
  LOGI("entry: KeyMint interceptor loading");
  teesim_control_start();
  bool ok = teesim_hook_install();
  LOGI("entry: KeyMint interceptor installed=%d (awaiting config push)", ok);
  return ok;
}
