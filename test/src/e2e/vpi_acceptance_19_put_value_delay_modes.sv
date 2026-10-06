// §38.34 (printed page 1125-1126) of IEEE 1800-2023: vpiNoDelay immediate;
// vpiInertialDelay scheduled; vpiReturnEvent yields a vpiSchedEvent with
// vpiScheduled; vpiCancelEvent cancels it. The library
// vpi_acceptance_19_put_value_delay_modes.c, built beside the run and named by
// vpi_acceptance_19_put_value_delay_modes.args, is the VPI application under
// test (#4338).
`timescale 1ns/1ns
module top;
  int v;
  always @(v) $display("v=%0d at %0t", v, $time);
  initial begin
    #1 $probe;
    #9 $display("end v=%0d at %0t", v, $time);
  end
endmodule
