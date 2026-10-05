// §38.34 (printed page 1126) of IEEE 1800-2023: vpiForceFlag overrides the
// continuous driver; vpiReleaseFlag restores it and returns the released value.
// The library vpi_acceptance_20_put_value_force_release.c, built beside the run
// and named by vpi_acceptance_20_put_value_force_release.args, is the VPI
// application under test (#4338).
`timescale 1ns/1ns
module top;
  logic d = 1;
  wire w = d;
  always @(w) $display("w=%0d at %0t", w, $time);
  initial begin
    #1 $probe;
    #1 $display("sv sees %0d at %0t", w, $time);
    #1 $probe;
    #1;
  end
endmodule
