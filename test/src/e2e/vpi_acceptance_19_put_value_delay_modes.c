/* §38.34: vpiNoDelay writes at once; vpiInertialDelay schedules after the
 * given time; vpiReturnEvent yields a vpiSchedEvent handle whose
 * vpiScheduled is 1 until it occurs or is cancelled with vpiCancelEvent. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle v = by_name("top.v", 0), ev;
  s_vpi_value val;
  s_vpi_time t;
  val.format = vpiIntVal;
  t.type = vpiSimTime; t.high = 0;
  val.value.integer = 5;
  vpi_printf("nodelay ret=%s\n", vpi_put_value(v, &val, 0, vpiNoDelay) ? "handle" : "null");
  val.value.integer = 6; t.low = 3;
  vpi_put_value(v, &val, &t, vpiInertialDelay);
  val.value.integer = 7; t.low = 6;
  ev = vpi_put_value(v, &val, &t, vpiTransportDelay | vpiReturnEvent);
  vpi_printf("event=%s type=%s scheduled=%d\n", ev ? "handle" : "null", str_of(vpiType, ev), vpi_get(vpiScheduled, ev));
  vpi_put_value(ev, 0, 0, vpiCancelEvent);
  vpi_printf("after cancel scheduled=%d err=%d\n", vpi_get(vpiScheduled, ev), vpi_chk_error(0) > 0);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
