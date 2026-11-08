module drv(output logic o); initial o = 1; endmodule
module rcv(input logic i); endmodule
module top;
  wire w, z;
  drv src(.o(w));
  rcv dst(.i(w));
  rcv other(.i(z));
  initial #1 $probe;
endmodule
