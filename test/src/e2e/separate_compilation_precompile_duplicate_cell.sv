// §33.3.1 (printed page 937) requires a warning when two modules of one name
// are mapped into one library in a single invocation. This file holds two
// modules named sc_dup, so the precompile warns once and exits 0. The .before
// step has already compiled the same file into the same library, and that
// earlier invocation's cells are replaced rather than counted, so they draw no
// second warning.
module sc_dup;
  initial $display("first");
endmodule

module sc_dup;
  initial $display("second");
endmodule
