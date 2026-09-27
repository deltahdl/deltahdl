// A precompile whose --precompile-out names a file in a directory that does not
// exist cannot persist the library §33.5.3 (printed page 944) requires, so it
// reports that it could not precompile the source and exits 1.
module sc_leaf;
  initial $display("leaf ran");
endmodule
