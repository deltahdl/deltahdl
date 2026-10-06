/* §38.36.1: cbForce/cbRelease fire after a force or release on a variable
 * with the resulting value; cbDisable fires when a named block is disabled;
 * placing cbForce on a variable bit-select is illegal. */
#include "vpi_probe.h"
static PLI_INT32 say(p_cb_data cb) {
  vpi_printf("%s value=%d at %u\n", cb->user_data, cb->value ? cb->value->value.integer : -1, (unsigned)cb->time->low);
  return 0;
}
static PLI_INT32 dis(p_cb_data cb) { vpi_printf("disabled %s at %u\n", str_of(vpiName, cb->obj), (unsigned)cb->time->low); return 0; }
static PLI_INT32 arm(p_cb_data cb) {
  vpiHandle bad;
  reg_cb(cbForce, say, by_name("top.x", 0), 0, (PLI_BYTE8*)"force");
  reg_cb(cbRelease, say, by_name("top.x", 0), 0, (PLI_BYTE8*)"release");
  reg_cb(cbDisable, dis, by_name("top.blk", 0), 0, 0);
  bad = reg_cb(cbForce, say, vpi_handle_by_index(by_name("top.v", 0), 0), 0, (PLI_BYTE8*)"bit");
  vpi_printf("cbForce on bit-select: %s err=%d\n", bad ? "handle" : "null", vpi_chk_error(0) > 0);
  return 0;
}
static void startup(void) { reg_cb(cbStartOfSimulation, arm, 0, 0, 0); }
STARTUP(startup);
