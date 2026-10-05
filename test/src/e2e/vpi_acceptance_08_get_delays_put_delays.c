/* §38.10, §38.32: vpi_get_delays() reads a continuous assignment's rise and
 * fall delays with no_of_delays 2; vpi_put_delays() replaces them and the
 * next transition uses the new delay. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle it = vpi_iterate(vpiContAssign, by_name("top", 0));
  vpiHandle ca = vpi_scan(it);
  s_vpi_time t[2];
  s_vpi_delay d;
  vpi_free_object(it);
  d.da = t; d.no_of_delays = 2; d.time_type = vpiSimTime; d.mtm_flag = 0; d.append_flag = 0; d.pulsere_flag = 0;
  vpi_get_delays(ca, &d);
  vpi_printf("delays %u %u\n", (unsigned)t[0].low, (unsigned)t[1].low);
  t[0].low = 5; t[1].low = 6; t[0].high = t[1].high = 0;
  vpi_put_delays(ca, &d);
  vpi_get_delays(ca, &d);
  vpi_printf("now %u %u\n", (unsigned)t[0].low, (unsigned)t[1].low);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
