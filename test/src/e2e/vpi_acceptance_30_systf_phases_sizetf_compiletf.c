/* §36.10.2, §38.37.1: after the startup routines the sizetf routines run,
 * then cbEndOfCompile; compiletf runs while the data structure is built,
 * before cbEndOfCompile; calltf runs at execution, after
 * cbStartOfSimulation; user_data reaches all three (§36.8.4). */
#include "vpi_probe.h"
static PLI_INT32 sizetf(PLI_BYTE8* ud) { vpi_printf("sizetf %s\n", ud); return 16; }
static PLI_INT32 compiletf(PLI_BYTE8* ud) { vpi_printf("compiletf %s\n", ud); return 0; }
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle call = vpi_handle(vpiSysTfCall, 0);
  s_vpi_value v; v.format = vpiIntVal; v.value.integer = 0xFFFF;
  vpi_put_value(call, &v, 0, vpiNoDelay);
  vpi_printf("calltf %s\n", ud);
  return 0;
}
static PLI_INT32 say(p_cb_data cb) { vpi_printf("%s\n", cb->user_data); return 0; }
static void startup(void) {
  s_vpi_systf_data d;
  memset(&d, 0, sizeof d);
  d.type = vpiSysFunc; d.sysfunctype = vpiSizedFunc; d.tfname = (PLI_BYTE8*)"$user_f";
  d.calltf = calltf; d.compiletf = compiletf; d.sizetf = sizetf; d.user_data = (PLI_BYTE8*)"ud";
  vpi_register_systf(&d);
  reg_cb(cbEndOfCompile, say, 0, 0, (PLI_BYTE8*)"end of compile");
  reg_cb(cbStartOfSimulation, say, 0, 0, (PLI_BYTE8*)"start of simulation");
}
STARTUP(startup);
