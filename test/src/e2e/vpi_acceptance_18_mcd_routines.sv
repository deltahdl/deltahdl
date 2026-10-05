// §38.24-§38.29 (printed page 1115-1119) of IEEE 1800-2023: vpi_mcd_open gives
// a one-bit descriptor other than 1; printf/vprintf return counts;
// vpi_mcd_name; flush and close return 0; descriptor 1 is stdout. The library
// vpi_acceptance_18_mcd_routines.c, built beside the run and named by
// vpi_acceptance_18_mcd_routines.args, is the VPI application under test
// (#4338).
module top;
  initial #1 $probe;
endmodule
