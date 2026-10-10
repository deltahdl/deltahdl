typedef logic [7:0] t;
module child;
`ifdef W
  int seen = 1;
`else
  int seen = 0;
`endif
  localparam int BW = $bits(t);
  int bw = BW;
endmodule
