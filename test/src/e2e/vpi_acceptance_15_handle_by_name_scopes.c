/* §38.21: a relative name resolves in the given scope, an absolute one from
 * the top with NULL, names reach into generate scopes and interface
 * instances, and an escaped identifier is named as written. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle sub = by_name("top.u", 0), g1 = by_name("top.g[1]", 0);
  vpi_printf("relative x in u=%d absolute=%d\n", int_of(by_name("x", sub)), int_of(by_name("top.u.x", 0)));
  vpi_printf("in generate=%d via scope=%d\n", int_of(by_name("top.g[1].y", 0)), int_of(by_name("y", g1)));
  vpi_printf("in interface=%d\n", int_of(by_name("top.i0.data", 0)));
  vpi_printf("escaped=%d\n", int_of(by_name("top.\\my-var ", 0)));
  vpi_printf("missing=%s wrong-scope=%s\n", by_name("top.nothing", 0) ? "handle" : "null",
             by_name("x", g1) ? "handle" : "null");
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
