// §38.4 (printed page 1091), §38.36.3 (printed page 1138) of IEEE 1800-2023:
// vpi_control(vpiFinish) ends the run; later events do not run;
// cbEndOfSimulation fires. The library vpi_acceptance_03_control_finish.c,
// built beside the run and named by vpi_acceptance_03_control_finish.args, is
// the VPI application under test (#4338).
`timescale 1ns/1ns
module top;
  initial begin
    $display("before");
    #5 $probe;
    #5 $display("after must not print");
  end
endmodule
