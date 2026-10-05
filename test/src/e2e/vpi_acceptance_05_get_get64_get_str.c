/* §38.6, §38.7, §38.11: vpi_get() for int and bool properties, vpi_get64()
 * for 64-bit ones, vpi_get_str() for strings including vpiType's name and
 * vpiDefName; the string buffer is the routine's and is overwritten. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle l = by_name("top.l", 0), s = by_name("top.s", 0), obj = vpi_handle(vpiClassObj, by_name("top.c", 0));
  PLI_BYTE8* first = vpi_get_str(vpiName, l);
  char copy[16];
  strncpy(copy, (const char*)first, 15); copy[15] = 0;
  vpi_get_str(vpiName, s);
  vpi_printf("l size=%d signed=%d type=%s name-copy=%s\n", vpi_get(vpiSize, l), vpi_get(vpiSigned, l),
             str_of(vpiType, l), copy);
  vpi_printf("objid64 nonzero=%d get(vpiType,obj)=%d(vpiClassObj=%d)\n", vpi_get64(vpiObjId, obj) != 0,
             vpi_get(vpiType, obj), vpiClassObj);
  char sub_def[16];
  strncpy(sub_def, str_of(vpiDefName, by_name("top.u", 0)), 15); sub_def[15] = 0;
  vpi_printf("s def=%s top def=%s\n", sub_def, str_of(vpiDefName, by_name("top", 0)));
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
