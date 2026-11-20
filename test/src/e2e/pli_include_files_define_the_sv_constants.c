#include <stdint.h>

#include "sv_vpi_user.h"

static PLI_INT32 calltf(PLI_BYTE8* user_data) {
  (void)user_data;
  vpiHandle inst = vpi_handle_by_name((PLI_BYTE8*)"t.u", 0);
  vpiHandle pkg = vpi_handle_by_name((PLI_BYTE8*)"p", 0);
  vpi_printf("interface %d\n", vpi_get(vpiType, inst) == vpiInterface);
  vpi_printf("package %d\n", vpi_get(vpiType, pkg) == vpiPackage);
  return 0;
}

static void startup(void) {
  s_vpi_systf_data data = {vpiSysTask, 0, (PLI_BYTE8*)"$probe", calltf, 0,
                           0,          0};
  vpi_register_systf(&data);
}

void (*vlog_startup_routines[])(void) = {startup, 0};
