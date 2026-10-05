// §38.2, Table 38-1 (printed pages 1088-1089) of IEEE 1800-2023: vpi_chk_error
// returns a severity after a failed routine, 0 after a successful one,
// unchanged by its own call, with state vpiRun and a message. The library
// vpi_acceptance_01_chk_error.c, built beside the run and named by
// vpi_acceptance_01_chk_error.args, is the VPI application under test (#4338).
module top;
  int x;
  initial #1 $probe;
endmodule
