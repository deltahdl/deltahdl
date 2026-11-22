module top;
`ifdef OUTER
`ifdef INNER
  initial #1 $probe;
`endif
`endif
endmodule
