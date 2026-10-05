// §38.22, §37.37 (printed page 1114, 1049) of IEEE 1800-2023:
// vpi_handle_multi(vpiInterModPath, out_port, in_port) gives the path a net
// connects; NULL when none. The library
// vpi_acceptance_16_handle_multi_intermod_path.c, built beside the run and
// named by vpi_acceptance_16_handle_multi_intermod_path.args, is the VPI
// application under test (#4338).
module drv(output logic o); initial o = 1; endmodule
module rcv(input logic i); endmodule
module top;
  wire w, z;
  drv src(.o(w));
  rcv dst(.i(w));
  rcv other(.i(z));
  initial #1 $probe;
endmodule
