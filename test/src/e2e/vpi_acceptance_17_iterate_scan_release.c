/* §38.23, §38.40, §38.38: vpi_iterate() returns NULL when there are no
 * objects; vpi_scan() returns NULL once and releases the iterator;
 * vpi_release_handle() returns 1 for a valid handle including an iterator
 * released early. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle top = by_name("top", 0), it, h;
  int n = 0;
  it = vpi_iterate(vpiVariables, top);
  while ((h = vpi_scan(it))) ++n;
  vpi_printf("vars=%d empty-iterate-null=%d\n", n, vpi_iterate(vpiNet, top) == 0);
  it = vpi_iterate(vpiVariables, top);
  h = vpi_scan(it);
  vpi_printf("release iterator early=%d release var=%d\n", vpi_release_handle(it),
             vpi_release_handle(h));
  vpi_printf("no error after releases=%d\n", vpi_chk_error(0) == 0);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
