// Preloaded into an instrumented executable, this hands glibc a main that
// returns kSkippedMainStatus at once in place of the program's own, a status
// the caller checks to know that the program's main did not run, since the
// loader only warns and runs the program whole when a preload fails. The static
// initializers of the executable and of every library it loads still run, and
// so does the exit handler the LLVM profiling runtime registers, so the process
// writes a whole profile holding only the counts of code that every run of the
// program executes before main.
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
