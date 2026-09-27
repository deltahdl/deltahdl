// Annex J.4 (printed page 1303): a well-formed bootstrap file named by
// -sv_liblist lists object code by location. With no -sv_root, J.3 resolves a
// relative entry against the working directory. The entry mylibs/lib1 names no
// shared library there, so the run reports it and exits with status 1 before
// the design runs.
module bootstrap_entry_missing_library;
  initial $display("ran");
endmodule
