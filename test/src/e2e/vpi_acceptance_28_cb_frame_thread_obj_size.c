/* §38.36.1, §37.17 detail 14: cbStartOfFrame/cbEndOfFrame bracket each
 * call of a task; cbStartOfThread/cbEndOfThread bracket each fork branch;
 * cbCreateObj fires once per new(); cbSizeChange fires on a queue with the
 * new size before the value change. */
#include "vpi_probe.h"
static int frames, threads, creates;
static PLI_INT32 sof(p_cb_data cb) { ++frames; return 0; }
static PLI_INT32 sot(p_cb_data cb) { ++threads; return 0; }
static PLI_INT32 co(p_cb_data cb) { ++creates; return 0; }
static PLI_INT32 sz(p_cb_data cb) { vpi_printf("size %d at %u\n", cb->value->value.integer, (unsigned)cb->time->low); return 0; }
static PLI_INT32 arm(p_cb_data cb) {
  vpiHandle it = vpi_iterate(vpiClassDefn, by_name("top", 0)), d = vpi_scan(it);
  vpi_free_object(it);
  reg_cb(cbStartOfFrame, sof, by_name("top.t", 0), 0, 0);
  reg_cb(cbStartOfThread, sot, 0, 0, 0);
  reg_cb(cbCreateObj, co, vpi_handle(vpiClassTypespec, d), 0, 0);
  reg_cb(cbSizeChange, sz, by_name("top.q", 0), 0, 0);
  return 0;
}
static PLI_INT32 eos(p_cb_data cb) { vpi_printf("frames %d threads>=%d creates %d\n", frames, threads >= 2, creates); return 0; }
static void startup(void) { reg_cb(cbStartOfSimulation, arm, 0, 0, 0); reg_cb(cbEndOfSimulation, eos, 0, 0, 0); }
STARTUP(startup);
