// §33.5.3 (printed page 944): --precompile-out names the file a separate
// compilation writes, and without --precompile-into the cells it would hold
// belong to no library, so the invocation is refused with status 1.
module sc_leaf;
  initial $display("leaf ran");
endmodule

module sc_top;
  sc_leaf u();
endmodule
