/* §38.31, §38.9: vpi_put_data() may be called only from a cbStartOfSave or
 * cbEndOfSave callback; elsewhere it fails, returning 0 with an error. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle call = vpi_handle(vpiSysTfCall, 0);
  PLI_BYTE8 scratch[8];
  PLI_INT32 rc = vpi_put_data(vpi_get(vpiSaveRestartID, call), (PLI_BYTE8*)"data", 4);
  int err = vpi_chk_error(0) > 0;
  vpi_printf("put_data outside save: rc=%d err=%d\n", rc, err);
  rc = vpi_get_data(vpi_get(vpiSaveRestartID, call), scratch, 4);
  vpi_printf("get_data outside restart: rc=%d err=%d\n", rc, vpi_chk_error(0) > 0);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
