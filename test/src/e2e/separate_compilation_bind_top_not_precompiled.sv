// §33.5.3 (printed page 944): every cell of a design is precompiled before
// the design is bound, so a --top naming a cell no loaded library holds is
// reported and the run exits 1.
module sc_leaf;
  initial $display("leaf ran");
endmodule

module sc_top;
  sc_leaf u();
endmodule
