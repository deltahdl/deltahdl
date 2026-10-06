/* §38.36.1: cbValueChange fires after each change with the new value and
 * the time; on an array member the index field holds the element index;
 * a change to the same value is not a change. */
#include "vpi_probe.h"
static PLI_INT32 vc(p_cb_data cb) {
  vpi_printf("%s -> %d at %u", cb->user_data, cb->value->value.integer, (unsigned)cb->time->low);
  if (vpi_get(vpiArrayMember, cb->obj)) vpi_printf(" index=%d", cb->index);
  vpi_printf("\n");
  return 0;
}
static PLI_INT32 arm(p_cb_data cb) {
  reg_cb(cbValueChange, vc, by_name("top.x", 0), 0, (PLI_BYTE8*)"x");
  reg_cb(cbValueChange, vc, vpi_handle_by_index(by_name("top.arr", 0), 2), 0, (PLI_BYTE8*)"arr[2]");
  return 0;
}
static void startup(void) { reg_cb(cbStartOfSimulation, arm, 0, 0, 0); }
STARTUP(startup);
