// §33.3.1 (printed page 935): the library map files an invocation names are
// read before any source file. Here the one named declares a library with no
// file path and no closing semicolon, which is not a library_declaration, so
// the map file's parse errors are reported and the run stops with status 1
// before this module is compiled.
module library_map_parse_error;
  initial $display("ran");
endmodule
