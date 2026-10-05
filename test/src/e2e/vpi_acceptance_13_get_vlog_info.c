/* §38.17: vpi_get_vlog_info() reports the invocation options, argv[0]
 * being the tool, and non-empty product and version strings. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  s_vpi_vlog_info info;
  int rc = vpi_get_vlog_info(&info), has_svlib = 0;
  for (int i = 0; i < info.argc; ++i) if (!strcmp(info.argv[i], "-sv_lib")) has_svlib = 1;
  vpi_printf("rc=%d argc>=4=%d argv0-ends-deltahdl=%d has-sv_lib=%d product=%d version=%d\n", rc,
             info.argc >= 4, strstr(info.argv[0], "deltahdl") != 0, has_svlib,
             info.product && *info.product, info.version && *info.version);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
