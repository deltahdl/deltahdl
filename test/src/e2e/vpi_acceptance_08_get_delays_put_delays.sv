// §38.10, §38.32 (printed page 1095, 1122) of IEEE 1800-2023: rise and fall
// delays of a continuous assignment read with no_of_delays 2; written delays
// take effect on the next transition. The library
// vpi_acceptance_08_get_delays_put_delays.c, built beside the run and named by
// vpi_acceptance_08_get_delays_put_delays.args, is the VPI application under
// test (#4338).
`timescale 1ns/1ns
module top;
  logic a = 0;
  wire y;
  assign #(3, 4) y = a;
  always @(y) $display("y=%0d at %0t", y, $time);
  initial begin
    #1 $probe;
    #9 a = 1;
    #10 a = 0;
    #10;
  end
endmodule
