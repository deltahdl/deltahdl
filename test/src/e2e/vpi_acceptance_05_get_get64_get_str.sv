// §38.6, §38.7, §38.11 (printed page 1092-1093, 1097) of IEEE 1800-2023:
// int/bool properties, 64-bit vpiObjId, string properties including vpiType's
// name and vpiDefName; the string buffer is overwritten by the next call. The
// library vpi_acceptance_05_get_get64_get_str.c, built beside the run and named
// by vpi_acceptance_05_get_get64_get_str.args, is the VPI application under
// test (#4338).
class C; endclass
module subdef; endmodule
module top;
  longint l; shortint s;
  C c = new;
  subdef u();
  initial #1 $probe;
endmodule
