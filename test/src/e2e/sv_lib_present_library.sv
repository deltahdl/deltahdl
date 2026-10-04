// Annex J.4 (printed page 1303): object code named by -sv_lib comes as a
// shared library with the platform's extension. The e2e runner builds
// sv_lib_present_library.c beside the run into that library, and
// sv_lib_present_library.args names it without the extension, so the
// presence check finds the file and the run goes on past it.
module t;
  initial $display("ran past the library check");
endmodule
