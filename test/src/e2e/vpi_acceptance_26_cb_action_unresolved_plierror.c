/* §38.36.3, §36.10.2: cbEndOfCompile, cbStartOfSimulation and
 * cbEndOfSimulation fire in that order; cbUnresolvedSystf fires for a
 * $name no application registered; cbPLIError fires when a VPI routine
 * fails. */
#include "vpi_probe.h"
static PLI_INT32 say(p_cb_data cb) { vpi_printf("%s\n", cb->user_data); return 0; }
static PLI_INT32 unresolved(p_cb_data cb) { vpi_printf("unresolved %s\n", cb->user_data ? cb->user_data : (PLI_BYTE8*)"?"); return 0; }
static PLI_INT32 plierr(p_cb_data cb) { vpi_printf("pli error callback\n"); return 0; }
static PLI_INT32 calltf(PLI_BYTE8* ud) { by_name("top.no_such", 0); return 0; }
static void startup(void) {
  reg_cb(cbEndOfCompile, say, 0, 0, (PLI_BYTE8*)"end of compile");
  reg_cb(cbStartOfSimulation, say, 0, 0, (PLI_BYTE8*)"start of simulation");
  reg_cb(cbEndOfSimulation, say, 0, 0, (PLI_BYTE8*)"end of simulation");
  reg_cb(cbUnresolvedSystf, unresolved, 0, 0, 0);
  reg_cb(cbPLIError, plierr, 0, 0, 0);
  reg_task("$probe", calltf, 0);
}
STARTUP(startup);
