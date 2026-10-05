/* §38.2, Table 38-1: vpi_chk_error() returns the severity of the previous
 * routine's error, 0 when there was none; the status is reset by any routine
 * but vpi_chk_error() itself; s_vpi_error_info.state is vpiRun at run time. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  s_vpi_error_info e;
  vpiHandle h = by_name("top.no_such", 0);
  int sev = vpi_chk_error(&e), again = vpi_chk_error(0);
  vpi_printf("bad name: %s sev>0=%d same-twice=%d state=%s message=%s\n", h ? "handle" : "null",
             sev > 0, sev == again, e.state == vpiRun ? "vpiRun" : "other", e.message ? "yes" : "no");
  by_name("top.x", 0);
  vpi_printf("after good call: %d\n", vpi_chk_error(0));
  vpi_get(vpiSize, 0);
  vpi_printf("vpi_get on NULL: sev>0=%d\n", vpi_chk_error(0) > 0);
  vpi_handle(vpiExpr, by_name("top.x", 0));
  vpi_printf("undefined relation: sev>0=%d\n", vpi_chk_error(0) > 0);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
