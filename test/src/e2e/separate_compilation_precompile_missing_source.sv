// A precompile whose second source cannot be opened stops there with status 1.
// The .before step precompiles this file first, which runs the case in a
// directory of its own so the library written ahead of the failure lands there.
module sc_leaf;
  initial $display("leaf ran");
endmodule

module sc_top;
  sc_leaf u();
endmodule
