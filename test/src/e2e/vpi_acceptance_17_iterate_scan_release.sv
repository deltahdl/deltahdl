// §38.23, §38.40, §38.38 (printed page 1114, 1145, 1144) of IEEE 1800-2023:
// empty iteration is NULL; vpi_scan releases the iterator at its end;
// vpi_release_handle and vpi_free_object return 1. The library
// vpi_acceptance_17_iterate_scan_release.c, built beside the run and named by
// vpi_acceptance_17_iterate_scan_release.args, is the VPI application under
// test (#4338).
module top;
  int a, b, c;
  initial #1 $probe;
endmodule
