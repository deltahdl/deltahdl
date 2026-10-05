// §38.21 (printed page 1113) of IEEE 1800-2023: relative names in a scope,
// absolute names with NULL, names into generate scopes and interface instances,
// an escaped identifier as written, missing names NULL. The library
// vpi_acceptance_15_handle_by_name_scopes.c, built beside the run and named by
// vpi_acceptance_15_handle_by_name_scopes.args, is the VPI application under
// test (#4338).
interface ifc; int data = 8; endinterface
module sub; int x = 5; endmodule
module top;
  sub u();
  ifc i0();
  int \my-var  = 3;
  for (genvar i = 0; i < 2; i++) begin : g
    int y = 10 + i;
  end
  initial #1 $probe;
endmodule
