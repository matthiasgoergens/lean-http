/* Preloaded into net-client: on SIGSEGV, prints the faulting thread's backtrace (module and offset,
   for addr2line) to stderr, then dies of the signal as before.  Lean's runtime installs a SIGSEGV
   handler of its own (to report stack overflows), so a later sigaction for SIGSEGV is ignored. */
#define _GNU_SOURCE
#include <execinfo.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>
#include <dlfcn.h>
#include <stdio.h>

static void handler(int sig, siginfo_t *info, void *ctx) {
  (void)ctx;
  void *frames[64];
  char line[128];
  int n = backtrace(frames, 64);
  int len = snprintf(line, sizeof line, "SIGSEGV at address %p, thread %d, %d frames:\n",
                     info->si_addr, (int)gettid(), n);
  write(2, line, len);
  for (int i = 0; i < n; i++) {
    Dl_info d;
    if (dladdr(frames[i], &d) && d.dli_fname) {
      len = snprintf(line, sizeof line, "  %p %s+0x%lx\n", frames[i], d.dli_fname,
                     (unsigned long)((char *)frames[i] - (char *)d.dli_fbase));
    } else {
      len = snprintf(line, sizeof line, "  %p\n", frames[i]);
    }
    write(2, line, len);
  }
  signal(sig, SIG_DFL);
  raise(sig);
}

static int installed = 0;

int sigaction(int signum, const struct sigaction *act, struct sigaction *old) {
  static int (*real)(int, const struct sigaction *, struct sigaction *) = NULL;
  if (!real) real = dlsym(RTLD_NEXT, "sigaction");
  if (installed && signum == SIGSEGV && act != NULL) {
    if (old) real(signum, NULL, old);
    return 0;
  }
  return real(signum, act, old);
}

__attribute__((constructor)) static void install(void) {
  static char stack[65536];
  stack_t ss = { .ss_sp = stack, .ss_size = sizeof stack, .ss_flags = 0 };
  sigaltstack(&ss, NULL);
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_sigaction = handler;
  sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
  sigaction(SIGSEGV, &sa, NULL);
  installed = 1;
}
