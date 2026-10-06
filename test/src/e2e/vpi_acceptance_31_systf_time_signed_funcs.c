/* §38.37.1: vpiTimeFunc returns a time put with vpiTimeVal;
 * vpiSizedSignedFunc returns a signed result of the sizetf width, so an
 * 8-bit all-ones is -1 to SystemVerilog and 255 through vpiSizedFunc. */
#include "vpi_probe.h"
static PLI_INT32 size8(PLI_BYTE8* ud) { return 8; }
static PLI_INT32 timef(PLI_BYTE8* ud) {
  s_vpi_value v; s_vpi_time t;
  t.type = vpiSimTime; t.high = 1; t.low = 5;
  v.format = vpiTimeVal; v.value.time = &t;
  vpi_put_value(vpi_handle(vpiSysTfCall, 0), &v, 0, vpiNoDelay);
  return 0;
}
static PLI_INT32 ones(PLI_BYTE8* ud) {
  s_vpi_value v; v.format = vpiIntVal; v.value.integer = -1;
  vpi_put_value(vpi_handle(vpiSysTfCall, 0), &v, 0, vpiNoDelay);
  return 0;
}
static void startup(void) {
  reg_func("$user_time", vpiTimeFunc, timef, 0);
  reg_func("$user_s8", vpiSizedSignedFunc, ones, size8);
  reg_func("$user_u8", vpiSizedFunc, ones, size8);
}
STARTUP(startup);
