/* §38.36.2: in cbReadWriteSynch a value may be written and scheduled; in
 * cbReadOnlySynch writing a value or scheduling an event is not allowed, so
 * vpi_put_value() fails with an error and the variable keeps its value. */
#include "vpi_probe.h"
static PLI_INT32 rw(p_cb_data cb) {
  s_vpi_value v; v.format = vpiIntVal; v.value.integer = 3;
  vpi_put_value(by_name("top.x", 0), &v, 0, vpiNoDelay);
  vpi_printf("rw write err=%d x=%d\n", vpi_chk_error(0) > 0, int_of(by_name("top.x", 0)));
  return 0;
}
static PLI_INT32 ro(p_cb_data cb) {
  s_vpi_value v; v.format = vpiIntVal; v.value.integer = 4;
  vpi_put_value(by_name("top.x", 0), &v, 0, vpiNoDelay);
  vpi_printf("ro write err=%d x=%d\n", vpi_chk_error(0) > 0, int_of(by_name("top.x", 0)));
  return 0;
}
static PLI_INT32 arm(p_cb_data cb) {
  reg_cb(cbReadWriteSynch, rw, 0, 2, 0);
  reg_cb(cbReadOnlySynch, ro, 0, 2, 0);
  return 0;
}
static void startup(void) { reg_cb(cbStartOfSimulation, arm, 0, 0, 0); }
STARTUP(startup);
