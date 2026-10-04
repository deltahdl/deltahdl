/* §36.6, Annex K.1 and Annex I: the library
 * vpi_routines_reach_a_loaded_library.sv names with -sv_lib. Its constructor
 * runs as deltahdl loads it and reports whether code in the library reaches
 * the routines the tool provides -- VPI's (Annex K) and svdpi.h's (Annex I) --
 * among the process's global symbols. It calls none of them, so it loads
 * whatever the tool provides. */
#include <dlfcn.h>
#include <stdio.h>

__attribute__((constructor)) static void report_symbols(void) {
  const char* names[] = {"vpi_register_systf", "vpi_register_cb",
                         "vpi_handle",         "vpi_printf",
                         "svDpiVersion",       "svGetScope",
                         0};
  for (int i = 0; names[i] != 0; ++i) {
    fprintf(stderr, "SYMBOL %s: %s\n", names[i],
            dlsym(RTLD_DEFAULT, names[i]) != 0 ? "found" : "absent");
  }
}
