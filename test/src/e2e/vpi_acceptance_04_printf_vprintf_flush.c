/* §38.30, §38.41, §38.5: vpi_printf() returns the number of characters
 * written, vpi_vprintf() takes a va_list, vpi_flush() returns 0 on success. */
#include "vpi_probe.h"
#include <stdarg.h>
static PLI_INT32 say(const char* fmt, ...) {
  va_list ap; PLI_INT32 n;
  va_start(ap, fmt); n = vpi_vprintf((PLI_BYTE8*)fmt, ap); va_end(ap);
  return n;
}
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  PLI_INT32 n = vpi_printf("hello %d\n", 42);
  PLI_INT32 m = say("via vprintf %s\n", "ok");
  vpi_printf("counts %d %d flush=%d\n", n, m, vpi_flush());
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
