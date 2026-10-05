/* §38.27, §38.28, §38.29, §38.26, §38.25, §38.24: vpi_mcd_open() returns a
 * descriptor with one bit set that is not the stdout descriptor 1,
 * vpi_mcd_printf()/vpi_mcd_vprintf() write to it, vpi_mcd_name() gives the
 * file name, vpi_mcd_flush() and vpi_mcd_close() return 0, and the file
 * holds what was written. */
#include "vpi_probe.h"
#include <stdarg.h>
static PLI_INT32 vsay(PLI_UINT32 mcd, const char* fmt, ...) {
  va_list ap; PLI_INT32 n;
  va_start(ap, fmt); n = vpi_mcd_vprintf(mcd, (PLI_BYTE8*)fmt, ap); va_end(ap);
  return n;
}
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  const char* path = "18-mcd-routines.txt";
  PLI_UINT32 mcd = vpi_mcd_open((PLI_BYTE8*)path);
  char buf[64] = {0};
  FILE* f;
  vpi_printf("mcd nonzero=%d not-stdout=%d one-bit=%d\n", mcd != 0, mcd != 1, (mcd & (mcd - 1)) == 0);
  vpi_printf("printf=%d vprintf=%d name-matches=%d flush=%d\n", vpi_mcd_printf(mcd, "line %d\n", 1),
             vsay(mcd, "line %d\n", 2), !strcmp((const char*)vpi_mcd_name(mcd), path), vpi_mcd_flush(mcd));
  vpi_printf("close=%d\n", vpi_mcd_close(mcd));
  f = fopen(path, "r");
  if (f) { size_t n = fread(buf, 1, 63, f); buf[n] = 0; fclose(f); }
  for (char* p = buf; *p; ++p) if (*p == '\n') *p = '|';
  vpi_printf("file=%s\n", buf);
  vpi_printf("stdout via mcd 1: %d\n", vpi_mcd_printf(1, "to stdout\n"));
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
