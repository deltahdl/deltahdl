#define _GNU_SOURCE
#include <dlfcn.h>

typedef int (*MainFunction)(int, char**, char**);
typedef int (*LibcStartMain)(MainFunction, int, char**, void (*)(void),
                             void (*)(void), void (*)(void), void*);

enum { kSkippedMainStatus = 77 };

static int SkipMain(int argc, char** argv, char** envp) {
  (void)argc;
  (void)argv;
  (void)envp;
  return kSkippedMainStatus;
}

int __libc_start_main(MainFunction main, int argc, char** argv,
                      void (*init)(void), void (*fini)(void),
                      void (*rtld_fini)(void), void* stack_end) {
  (void)main;
  LibcStartMain next = (LibcStartMain)dlsym(RTLD_NEXT, "__libc_start_main");
  return next(SkipMain, argc, argv, init, fini, rtld_fini, stack_end);
}
