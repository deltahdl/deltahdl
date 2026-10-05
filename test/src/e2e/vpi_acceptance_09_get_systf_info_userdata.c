/* §38.12, §38.33, §38.14: vpi_get_systf_info() on the call handle gives the
 * registered tfname, type and user_data; vpi_put_userdata()/vpi_get_userdata()
 * attach data to one call instance and not to another. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle call = vpi_handle(vpiSysTfCall, 0);
  s_vpi_systf_data info;
  void* prev = vpi_get_userdata(call);
  vpi_get_systf_info(call, &info);
  vpi_printf("%s type=%s user_data=%s line=%d prev=%s\n", info.tfname,
             info.type == vpiSysTask ? "task" : "func", info.user_data, vpi_get(vpiLineNo, call),
             prev ? (const char*)prev : "none");
  if (!prev) vpi_printf("put_userdata=%d\n", vpi_put_userdata(call, (void*)"stored"));
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, (PLI_BYTE8*)"registered"); }
STARTUP(startup);
