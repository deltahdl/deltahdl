// §38.17 (printed page 1110) of IEEE 1800-2023: argc/argv of the invocation
// including -sv_lib, product and version strings. The library
// vpi_acceptance_13_get_vlog_info.c, built beside the run and named by
// vpi_acceptance_13_get_vlog_info.args, is the VPI application under test
// (#4338).
module top;
  initial #1 $probe;
endmodule
