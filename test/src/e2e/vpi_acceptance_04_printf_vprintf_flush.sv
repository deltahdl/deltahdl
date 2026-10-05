// §38.30, §38.41, §38.5 (printed page 1119, 1146, 1092) of IEEE 1800-2023:
// vpi_printf returns the character count; vpi_vprintf takes a va_list;
// vpi_flush returns 0. The library vpi_acceptance_04_printf_vprintf_flush.c,
// built beside the run and named by
// vpi_acceptance_04_printf_vprintf_flush.args, is the VPI application under
// test (#4338).
module top;
  initial #1 $probe;
endmodule
