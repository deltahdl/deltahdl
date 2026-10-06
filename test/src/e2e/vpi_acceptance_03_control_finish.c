/* §38.4: vpi_control(vpiFinish, 0) ends the simulation; later events do not
 * run, and cbEndOfSimulation still fires (§38.36.3). */
#include "vpi_probe.h"
static PLI_INT32 eos(p_cb_data cb) { vpi_printf("end at %u\n", (unsigned)now_low()); return 0; }
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpi_printf("finishing at %u\n", (unsigned)now_low());
  vpi_control(vpiFinish, 0);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); reg_cb(cbEndOfSimulation, eos, 0, 0, 0); }
STARTUP(startup);
