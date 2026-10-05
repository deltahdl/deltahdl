/* §38.8, §38.39: vpi_get_cb_info() returns the registered reason, object
 * and user_data; vpi_remove_cb() returns 1 and the callback never fires. */
#include "vpi_probe.h"
static int fired;
static vpiHandle cbh;
static PLI_INT32 vc(p_cb_data cb) { ++fired; vpi_printf("value change %d at %u\n", cb->value->value.integer, (unsigned)cb->time->low); return 0; }
static PLI_INT32 arm(p_cb_data cb) { cbh = reg_cb(cbValueChange, vc, by_name("top.x", 0), 0, (PLI_BYTE8*)"ud"); return 0; }
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  s_cb_data info;
  vpi_get_cb_info(cbh, &info);
  vpi_printf("info reason=%s obj=%s user_data=%s\n", info.reason == cbValueChange ? "cbValueChange" : "?",
             str_of(vpiName, info.obj), info.user_data);
  vpi_printf("remove=%d fired-so-far=%d\n", vpi_remove_cb(cbh), fired);
  return 0;
}
static PLI_INT32 eos(p_cb_data cb) { vpi_printf("fired total=%d\n", fired); return 0; }
static void startup(void) {
  reg_cb(cbStartOfSimulation, arm, 0, 0, 0);
  reg_cb(cbEndOfSimulation, eos, 0, 0, 0);
  reg_task("$probe", calltf, 0);
}
STARTUP(startup);
