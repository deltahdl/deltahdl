#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle mem = by_name("top.mem", 0);
  vpiHandle word = mem ? vpi_handle_by_index(mem, 0) : 0;
  vpi_printf("memory=%d word=%d\n", mem ? vpi_get(vpiType, mem) : -1,
             word ? vpi_get(vpiType, word) : -1);
  print_names("variables", vpiVariables, by_name("top", 0));
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
