// §38.31, §38.9 (printed page 1120, 1094) of IEEE 1800-2023: outside
// cbStartOfSave/cbEndOfSave vpi_put_data fails with 0 and an error;
// vpi_get_data outside a restart likewise. The library
// vpi_acceptance_07_put_data_get_data.c, built beside the run and named by
// vpi_acceptance_07_put_data_get_data.args, is the VPI application under test
// (#4338).
module top;
  initial #1 $probe;
endmodule
