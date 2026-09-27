// §33.5.3 (printed page 944): a separate compilation tool compiles source
// descriptions into a library whose compiled forms persist in the filesystem.
// --precompile-into names the library and --precompile-out the file that holds
// it, and one without the other leaves either no file or no library, so the
// invocation is refused with status 1.
module sc_leaf;
  initial $display("leaf ran");
endmodule

module sc_top;
  sc_leaf u();
endmodule
