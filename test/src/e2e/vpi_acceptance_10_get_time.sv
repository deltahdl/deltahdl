// §38.13 (printed page 1099) of IEEE 1800-2023: vpiSimTime in precision units;
// vpiScaledRealTime in the object's time unit. The library
// vpi_acceptance_10_get_time.c, built beside the run and named by
// vpi_acceptance_10_get_time.args, is the VPI application under test (#4338).
`timescale 1ns/1ps
module sub; timeunit 1ps; timeprecision 1ps; endmodule
module top;
  sub s();
  initial #7 $probe;
endmodule
