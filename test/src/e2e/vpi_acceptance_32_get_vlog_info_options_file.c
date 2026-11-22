#include "vpi_probe.h"
static void show(const char* label, PLI_BYTE8** words) {
  int i = 0;
  vpi_printf("%s:", label);
  for (; words[i]; ++i) {
    int nested = i > 0 && !strcmp(words[i - 1], "-f");
    vpi_printf(" [%d]=%s", i, nested ? "(array)" : words[i]);
  }
  vpi_printf(" [%d]=NULL\n", i);
}
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  s_vpi_vlog_info info;
  int rc = vpi_get_vlog_info(&info), at = -1;
  for (int i = 0; i + 1 < info.argc; ++i)
    if (!strcmp(info.argv[i], "-f")) at = i;
  vpi_printf("rc=%d option-found=%d\n", rc, at >= 0);
  if (at < 0) return 0;
  PLI_BYTE8** outer = (PLI_BYTE8**)info.argv[at + 1];
  show("outer", outer);
  if (outer[1] && outer[2] && !strcmp(outer[2], "-f"))
    show("inner", (PLI_BYTE8**)outer[3]);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
