/* §38.34 x §37.33 x §9.4: vpi_put_value() on a property of a class object,
 * reached obj -> vpiVariables, is seen by a class task blocked on
 * wait(val == 9) in the same time step. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle obj = vpi_handle(vpiClassObj, by_name("top.c", 0));
  vpiHandle it = vpi_iterate(vpiVariables, obj), v;
  s_vpi_value val;
  val.format = vpiIntVal;
  val.value.integer = 9;
  while ((v = vpi_scan(it)))
    if (!strcmp(str_of(vpiName, v), "val")) {
      vpi_printf("put val=9 at %u\n", (unsigned)now_low());
      vpi_put_value(v, &val, 0, vpiNoDelay);
      if (vpi_chk_error(0)) vpi_printf("put failed\n");
    }
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
