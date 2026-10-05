/* Helpers shared by the vpi_acceptance_* e2e cases (#4338). Each probe is a VPI
 * application (§36.6): a C file compiled to a shared library that the tool
 * loads, whose vlog_startup_routines[] entry (§36.9.1, §38.37.2) registers
 * system tasks and callbacks. */
#ifndef VPI_PROBE_H
#define VPI_PROBE_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sv_vpi_user.h"

#define STARTUP(fn) void (*vlog_startup_routines[])(void) = {fn, 0}

static const char* str_of(int prop, vpiHandle h) {
  PLI_BYTE8* s = h ? vpi_get_str(prop, h) : 0;
  return s ? (const char*)s : "(null)";
}
static int int_of(vpiHandle h) {
  s_vpi_value v;
  v.format = vpiIntVal;
  vpi_get_value(h, &v);
  return v.value.integer;
}
static vpiHandle by_name(const char* n, vpiHandle scope) {
  return vpi_handle_by_name((PLI_BYTE8*)n, scope);
}
static vpiHandle reg_task(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*),
                          PLI_BYTE8* user_data) {
  s_vpi_systf_data d;
  memset(&d, 0, sizeof d);
  d.type = vpiSysTask;
  d.tfname = (PLI_BYTE8*)name;
  d.calltf = calltf;
  d.user_data = user_data;
  return vpi_register_systf(&d);
}
static vpiHandle reg_func(const char* name, int functype,
                          PLI_INT32 (*calltf)(PLI_BYTE8*),
                          PLI_INT32 (*sizetf)(PLI_BYTE8*)) {
  s_vpi_systf_data d;
  memset(&d, 0, sizeof d);
  d.type = vpiSysFunc;
  d.sysfunctype = functype;
  d.tfname = (PLI_BYTE8*)name;
  d.calltf = calltf;
  d.sizetf = sizetf;
  return vpi_register_systf(&d);
}
static vpiHandle reg_cb(int reason, PLI_INT32 (*rtn)(p_cb_data), vpiHandle obj,
                        PLI_INT32 delay_low, PLI_BYTE8* user_data) {
  static s_vpi_time t;
  static s_vpi_value v;
  s_cb_data cb;
  t.type = vpiSimTime;
  t.high = 0;
  t.low = (PLI_UINT32)delay_low;
  v.format = vpiIntVal;
  memset(&cb, 0, sizeof cb);
  cb.reason = reason;
  cb.cb_rtn = rtn;
  cb.obj = obj;
  cb.time = &t;
  cb.value = &v;
  cb.user_data = user_data;
  return vpi_register_cb(&cb);
}
/* Collects the vpiName of every object an iteration yields, sorted, so that
 * a probe's expectation does not depend on the tool's iteration order. */
static int names_sorted(int type, vpiHandle ref, char out[][64], int max) {
  vpiHandle it = vpi_iterate(type, ref), h;
  int n = 0;
  if (!it) return 0;
  while ((h = vpi_scan(it)) && n < max) {
    strncpy(out[n], str_of(vpiName, h), 63);
    out[n][63] = 0;
    ++n;
  }
  for (int i = 1; i < n; ++i)
    for (int j = i; j > 0 && strcmp(out[j - 1], out[j]) > 0; --j) {
      char t[64];
      strcpy(t, out[j]);
      strcpy(out[j], out[j - 1]);
      strcpy(out[j - 1], t);
    }
  return n;
}
static void print_names(const char* label, int type, vpiHandle ref) {
  char names[32][64];
  int n = names_sorted(type, ref, names, 32);
  vpi_printf("%s: %d", label, n);
  for (int i = 0; i < n; ++i) vpi_printf(" %s", names[i]);
  vpi_printf("\n");
}
static PLI_UINT32 now_low(void) {
  s_vpi_time t;
  t.type = vpiSimTime;
  vpi_get_time(0, &t);
  return t.low;
}
#endif
