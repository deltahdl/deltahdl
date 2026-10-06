// §36.10.2 (printed page 990), §38.37.1 (printed page 1141), §36.8.4 (printed
// page 988) of IEEE 1800-2023: sizetf and compiletf run before cbEndOfCompile,
// calltf after cbStartOfSimulation; user_data reaches all three; the sized
// result is 16 bits. The library
// vpi_acceptance_30_systf_phases_sizetf_compiletf.c, built beside the run and
// named by vpi_acceptance_30_systf_phases_sizetf_compiletf.args, is the VPI
// application under test (#4338).
module top;
  initial $display("%0d %0d", $user_f(), $bits($user_f()));
endmodule
