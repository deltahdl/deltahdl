// §38.8, §38.39 (printed page 1093, 1144) of IEEE 1800-2023: vpi_get_cb_info
// returns the registered reason, obj and user_data; vpi_remove_cb returns 1 and
// stops the callback. The library vpi_acceptance_06_get_cb_info_remove_cb.c,
// built beside the run and named by
// vpi_acceptance_06_get_cb_info_remove_cb.args, is the VPI application under
// test (#4338).
`timescale 1ns/1ns
module top;
  int x;
  initial begin
    #1 x = 5;
    #1 x = 6;
    #1 $probe;
    #1 x = 7;
  end
endmodule
