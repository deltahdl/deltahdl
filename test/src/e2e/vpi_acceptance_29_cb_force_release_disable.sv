// §38.36.1 (printed page 1133, 1135) of IEEE 1800-2023: cbForce/cbRelease with
// the resulting value; cbDisable on a named block; cbForce on a bit-select is
// illegal. The library vpi_acceptance_29_cb_force_release_disable.c, built
// beside the run and named by vpi_acceptance_29_cb_force_release_disable.args,
// is the VPI application under test (#4338).
`timescale 1ns/1ns
module top;
  int x;
  logic [3:0] v;
  initial begin
    #1 force x = 5;
    #1 release x;
  end
  initial begin : blk
    #10 $display("blk ran on");
  end
  initial #3 disable blk;
endmodule
