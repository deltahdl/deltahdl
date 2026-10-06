/* §38.34: vpiForceFlag forces a net over its continuous driver;
 * vpiReleaseFlag releases it, the value then following the driver again
 * and value_p receiving the released value. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle w = by_name("top.w", 0);
  s_vpi_value val;
  val.format = vpiIntVal;
  val.value.integer = 0;
  if (now_low() == 1) {
    vpi_put_value(w, &val, 0, vpiForceFlag);
    vpi_printf("forced err=%d\n", vpi_chk_error(0) > 0);
  } else {
    vpi_put_value(w, &val, 0, vpiReleaseFlag);
    vpi_printf("released value=%d\n", val.value.integer);
  }
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
