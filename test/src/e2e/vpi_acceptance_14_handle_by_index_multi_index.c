/* §38.19, §38.20: vpi_handle_by_index() selects one element of a
 * one-dimensional array or one row of a multidimensional one;
 * vpi_handle_by_multi_index() selects with a full index array; an index out
 * of range gives NULL. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle m = by_name("top.m", 0), v = by_name("top.v", 0);
  PLI_INT32 i12[2] = {1, 2}, i01[2] = {0, 1};
  vpi_printf("m[1][2]=%d m[0][1]=%d m[1] row size=%d m[1][0]=%d\n",
             int_of(vpi_handle_by_multi_index(m, 2, i12)), int_of(vpi_handle_by_multi_index(m, 2, i01)),
             vpi_get(vpiSize, vpi_handle_by_index(m, 1)), int_of(vpi_handle_by_index(vpi_handle_by_index(m, 1), 0)));
  vpi_printf("v[5]=%d v[9]=%s\n", int_of(vpi_handle_by_index(v, 5)), vpi_handle_by_index(v, 9) ? "handle" : "null");
  vpi_printf("decl-range arr[3]=%d arr[0]=%s\n", int_of(vpi_handle_by_index(by_name("top.arr", 0), 3)),
             vpi_handle_by_index(by_name("top.arr", 0), 0) ? "handle" : "null");
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
