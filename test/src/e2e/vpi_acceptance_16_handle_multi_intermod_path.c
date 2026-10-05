/* §38.22, §37.37: vpi_handle_multi(vpiInterModPath, out_port, in_port)
 * gives the intermodule path between an output port and an input port that
 * one net connects; NULL when no such path exists. */
#include "vpi_probe.h"
static vpiHandle port_named(vpiHandle inst, const char* n) {
  vpiHandle it = vpi_iterate(vpiPort, inst), p;
  while ((p = vpi_scan(it))) if (!strcmp(str_of(vpiName, p), n)) { vpi_free_object(it); return p; }
  return 0;
}
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle o = port_named(by_name("top.src", 0), "o"), i = port_named(by_name("top.dst", 0), "i");
  vpiHandle j = port_named(by_name("top.other", 0), "i");
  vpiHandle path = vpi_handle_multi(vpiInterModPath, o, i, 0);
  vpi_printf("path=%s type=%s\n", path ? "handle" : "null", str_of(vpiType, path));
  vpi_printf("unconnected=%s\n", vpi_handle_multi(vpiInterModPath, o, j, 0) ? "handle" : "null");
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
