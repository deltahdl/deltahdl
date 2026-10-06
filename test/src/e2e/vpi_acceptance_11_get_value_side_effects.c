/* §37.3.5, §38.15: vpi_get_value() on an argument expression evaluates it
 * fully, side effects included, once per call. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle it = vpi_iterate(vpiArgument, vpi_handle(vpiSysTfCall, 0));
  vpiHandle a = vpi_scan(it);
  vpi_free_object(it);
  vpi_printf("arg type=%s value=%d\n", str_of(vpiType, a), int_of(a));
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
