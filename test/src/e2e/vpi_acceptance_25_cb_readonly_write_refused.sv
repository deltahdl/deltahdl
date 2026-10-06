// §38.36.2 (printed page 1137) of IEEE 1800-2023: a write in cbReadWriteSynch
// succeeds; in cbReadOnlySynch it is refused with an error and the value stays.
// The library vpi_acceptance_25_cb_readonly_write_refused.c, built beside the
// run and named by vpi_acceptance_25_cb_readonly_write_refused.args, is the VPI
// application under test (#4338).
`timescale 1ns/1ns
module top;
  int x;
  initial #3 $display("sv x=%0d at %0t", x, $time);
endmodule
