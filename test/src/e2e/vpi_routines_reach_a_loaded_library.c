#include <dlfcn.h>
#include <stdio.h>

__attribute__((constructor)) static void report_symbols(void) {
  const char* names[] = {"vpi_register_systf",
                         "vpi_register_cb",
                         "vpi_handle",
                         "vpi_printf",
                         "svDpiVersion",
                         "svGetScope",
                         0};
  for (int i = 0; names[i] != 0; ++i) {
    fprintf(stderr, "SYMBOL %s: %s\n", names[i],
            dlsym(RTLD_DEFAULT, names[i]) != 0 ? "found" : "absent");
  }
}
