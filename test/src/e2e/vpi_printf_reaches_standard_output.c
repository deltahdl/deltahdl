#include <stdarg.h>
#include <stdint.h>

#include "vpi_user.h"

static PLI_INT32 vprinted(const char* format, ...) {
  va_list args;
  va_start(args, format);
  PLI_INT32 count = vpi_vprintf((PLI_BYTE8*)format, args);
  va_end(args);
  return count;
}

static PLI_INT32 calltf(PLI_BYTE8* user_data) {
  (void)user_data;
  vpi_printf("in calltf %d\n", 1);
  vprinted("in calltf %d\n", 2);
  vpi_mcd_printf(1, "in calltf %d\n", 3);
  return 0;
}

static void startup(void) {
  s_vpi_systf_data data = {vpiSysTask, 0, (PLI_BYTE8*)"$probe", calltf, 0,
                           0,          0};
  vpi_printf("in startup\n");
  vpi_register_systf(&data);
}

void (*vlog_startup_routines[])(void) = {startup, 0};
