// LD_PRELOAD helper: on SIGSEGV/SIGABRT print a backtrace (module+offset) of the faulting thread to stderr.
#define _GNU_SOURCE
#include <execinfo.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
static void handler(int sig) {
  void *bt[64];
  int n = backtrace(bt, 64);
  const char msg[] = "\n!!! fatal signal, backtrace of faulting thread:\n";
  write(2, msg, sizeof msg - 1);
  backtrace_symbols_fd(bt, n, 2);
  _exit(128 + sig);
}
__attribute__((constructor)) static void init(void) {
  struct sigaction sa; memset(&sa, 0, sizeof sa);
  sa.sa_handler = handler; sigemptyset(&sa.sa_mask);
  sigaction(SIGSEGV, &sa, NULL); sigaction(SIGABRT, &sa, NULL); sigaction(SIGBUS, &sa, NULL);
}
