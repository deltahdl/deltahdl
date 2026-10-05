/* §38.13: vpi_get_time() with vpiSimTime gives the time in simulation
 * precision units and with vpiScaledRealTime in the units of the object. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  s_vpi_time t;
  vpiHandle top = by_name("top", 0), sub = by_name("top.s", 0);
  t.type = vpiSimTime; vpi_get_time(0, &t);
  vpi_printf("sim low=%u high=%u\n", (unsigned)t.low, (unsigned)t.high);
  t.type = vpiScaledRealTime; vpi_get_time(top, &t);
  vpi_printf("scaled top=%.3f\n", t.real);
  t.type = vpiScaledRealTime; vpi_get_time(sub, &t);
  vpi_printf("scaled sub=%.3f\n", t.real);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
