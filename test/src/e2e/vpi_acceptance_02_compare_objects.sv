// §38.3, §37.2.3 (printed page 1089, 999) of IEEE 1800-2023: handles to one
// object compare equal through the routine, handles to different objects do
// not. The library vpi_acceptance_02_compare_objects.c, built beside the run
// and named by vpi_acceptance_02_compare_objects.args, is the VPI application
// under test (#4338).
module top;
  int x, y;
  initial #1 $probe;
endmodule
