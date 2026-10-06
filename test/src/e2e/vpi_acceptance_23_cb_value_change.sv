// §38.36.1 (printed page 1133, 1135) of IEEE 1800-2023: cbValueChange after
// each change with value, time and (for an array member) index; no callback for
// a write of the same value. The library vpi_acceptance_23_cb_value_change.c,
// built beside the run and named by vpi_acceptance_23_cb_value_change.args, is
// the VPI application under test (#4338).
`timescale 1ns/1ns
module top;
  int x;
  int arr[4];
  initial begin
    #1 x = 5;
    #1 arr[2] = 8;
    #1 x = 5;
    #1 x = 6;
    #1 arr[1] = 9;
  end
endmodule
