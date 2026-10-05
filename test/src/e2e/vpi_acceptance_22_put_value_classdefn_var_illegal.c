/* §37.31 detail 2: vpi_get_value()/vpi_put_value() are not allowed on a
 * variable handle obtained from a class defn; each is an error reported by
 * vpi_chk_error(); the same var through the class obj is fine. */
#include "vpi_probe.h"
static PLI_INT32 calltf(PLI_BYTE8* ud) {
  vpiHandle it = vpi_iterate(vpiClassDefn, by_name("top", 0)), d = vpi_scan(it), v;
  vpiHandle vars = vpi_iterate(vpiVariables, d);
  s_vpi_value val;
  vpi_free_object(it);
  v = vpi_scan(vars);
  vpi_free_object(vars);
  val.format = vpiIntVal;
  vpi_get_value(v, &val);
  vpi_printf("get on defn var %s: err=%d\n", str_of(vpiName, v), vpi_chk_error(0) > 0);
  val.value.integer = 3;
  vpi_put_value(v, &val, 0, vpiNoDelay);
  vpi_printf("put on defn var: err=%d\n", vpi_chk_error(0) > 0);
  vars = vpi_iterate(vpiVariables, vpi_handle(vpiClassObj, by_name("top.c", 0)));
  v = vpi_scan(vars);
  vpi_get_value(v, &val);
  vpi_printf("get on obj var: value=%d err=%d\n", val.value.integer, vpi_chk_error(0) > 0);
  return 0;
}
static void startup(void) { reg_task("$probe", calltf, 0); }
STARTUP(startup);
