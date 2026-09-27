// Annex J.4 (printed page 1303): -sv_liblist names a bootstrap file to read.
// A file that cannot be opened is reported, and the run exits with status 1
// before the design runs.
module bootstrap_unopenable;
  initial $display("ran");
endmodule
