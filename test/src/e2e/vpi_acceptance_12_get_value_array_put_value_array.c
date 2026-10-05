/* §38.16, §38.35: vpi_get_value_array() reads a run of array elements into
 * one buffer, vpi_put_value_array() writes them with vpiNoDelay. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle arr = by_name("top.arr", 0);
  PLI_INT32 buf[4] = {0, 0, 0, 0}, idx = 0;
  s_vpi_arrayvalue av;
  memset(&av, 0, sizeof av);
  av.format = vpiIntVal;
  av.value.integers = buf;
  vpi_get_value_array(arr, &av, &idx, 4);
  vpi_printf("read %d %d %d %d\n", buf[0], buf[1], buf[2], buf[3]);
  for (int i = 0; i < 4; ++i) buf[i] = 50 + i;
  vpi_put_value_array(arr, &av, &idx, 4);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
