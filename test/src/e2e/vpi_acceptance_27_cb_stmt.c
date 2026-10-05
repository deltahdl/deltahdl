/* §38.36.1.1, §38.36.1.2, §38.36.1.3: cbStmt on a module places a callback
 * before every statement in it; the block itself counts once (Table 38-6),
 * a delay control once when encountered, and each assignment once. */
#include "vpi_probe.h"
static int stmts;
static PLI_INT32 st(p_cb_data cb) { ++stmts; vpi_printf("stmt %s\n", str_of(vpiType, cb->obj)); return 0; }
static PLI_INT32 arm(p_cb_data cb) {
  vpiHandle h = reg_cb(cbStmt, st, by_name("top", 0), 0, 0);
  vpi_printf("module-wide cbStmt handle=%s\n", h ? "one" : "null");
  return 0;
}
static PLI_INT32 eos(p_cb_data cb) { vpi_printf("statements %d\n", stmts); return 0; }
static void startup(void) { reg_cb(cbStartOfSimulation, arm, 0, 0, 0); reg_cb(cbEndOfSimulation, eos, 0, 0, 0); }
STARTUP(startup);
