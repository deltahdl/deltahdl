/* §38.36.2 x §4.4.2: in one time slice cbAtStartOfSimTime precedes the
 * Active events, cbNBASynch precedes the NBA update, cbAtEndOfSimTime and
 * cbReadOnlySynch follow the NBA update; cbNextSimTime fires before the
 * next time queue and cbAfterDelay after the given delay. */
#include "vpi_probe.h"
static PLI_INT32 say(p_cb_data cb) {
  vpi_printf("%s at %u q=%d\n", cb->user_data, (unsigned)cb->time->low, int_of(by_name("top.q", 0)));
  return 0;
}
static PLI_INT32 arm(p_cb_data cb) {
  reg_cb(cbAtStartOfSimTime, say, 0, 5, (PLI_BYTE8*)"start-of-5");
  reg_cb(cbNBASynch, say, 0, 5, (PLI_BYTE8*)"nba-synch-5");
  reg_cb(cbAtEndOfSimTime, say, 0, 5, (PLI_BYTE8*)"end-of-5");
  reg_cb(cbReadOnlySynch, say, 0, 5, (PLI_BYTE8*)"read-only-5");
  reg_cb(cbAfterDelay, say, 0, 7, (PLI_BYTE8*)"after-delay-7");
  reg_cb(cbNextSimTime, say, 0, 0, (PLI_BYTE8*)"next-sim-time");
  return 0;
}
static void startup(void) { reg_cb(cbStartOfSimulation, arm, 0, 0, 0); }
STARTUP(startup);
