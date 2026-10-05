/* §38.3, §37.2.3: two handles to one object compare equal by
 * vpi_compare_objects(), never by C ==; handles to different objects do not. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle a1 = by_name("top.x", 0), a2 = by_name("top.x", 0), b = by_name("top.y", 0);
  vpiHandle it = vpi_iterate(vpiVariables, by_name("top", 0)), h, viaiter = 0;
  while ((h = vpi_scan(it))) if (!strcmp(str_of(vpiName, h), "x")) viaiter = h;
  vpi_printf("same=%d via-iterate=%d different=%d\n", vpi_compare_objects(a1, a2),
             vpi_compare_objects(a1, viaiter), vpi_compare_objects(a1, b));
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
