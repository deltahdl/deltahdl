// §38.36.2 (printed page 1137-1138) x §4.4.2 of IEEE 1800-2023: in one slice
// cbAtStartOfSimTime precedes Active, cbNBASynch precedes the NBA update,
// cbAtEndOfSimTime and cbReadOnlySynch follow it; cbNextSimTime before the next
// queue; cbAfterDelay after a delay. The library
// vpi_acceptance_24_cb_time_regions.c, built beside the run and named by
// vpi_acceptance_24_cb_time_regions.args, is the VPI application under test
// (#4338).
`timescale 1ns/1ns
module top;
  int q;
  initial begin
    #5;
    $display("active at %0t q=%0d", $time, q);
    q <= 1;
    #5;
  end
endmodule
