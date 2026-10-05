/* §38.30, §38.41 and §38.27: the library vpi_printf_reaches_standard_output.sv
 * names with -sv_lib. It prints through vpi_printf from its startup routine,
 * through vpi_vprintf and through vpi_mcd_printf on channel 1 from the calltf
 * of the system task $probe it registers, each of which writes to the output
 * channel of the tool, in order with the design's own output. */
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
  s_vpi_systf_data data = {vpiSysTask, 0, (PLI_BYTE8*)"$probe", calltf, 0, 0,
                           0};
  vpi_printf("in startup\n");
  vpi_register_systf(&data);
}

void (*vlog_startup_routines[])(void) = {startup, 0};
