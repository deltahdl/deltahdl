// The same duplicate as separate_compilation_precompile_duplicate_cell, run
// with -Werror: the §33.3.1 warning is reported as an error and the precompile
// exits 1.
module sc_dup;
  initial $display("first");
endmodule

module sc_dup;
  initial $display("second");
endmodule
