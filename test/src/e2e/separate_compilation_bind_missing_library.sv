// §33.5.4 (printed page 944): a bind takes its cells from precompiled
// libraries alone, so a --load-lib naming no library file is refused with
// status 1 before anything is bound.
module sc_leaf;
  initial $display("leaf ran");
endmodule

module sc_top;
  sc_leaf u();
endmodule
