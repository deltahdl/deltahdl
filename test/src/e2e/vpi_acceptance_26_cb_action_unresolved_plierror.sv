// §38.36.3 (printed page 1138-1139), §36.10.2 (printed page 990) of IEEE
// 1800-2023: cbEndOfCompile, cbStartOfSimulation, cbEndOfSimulation in order;
// cbUnresolvedSystf for an unregistered $name; cbPLIError when a routine fails.
// The library vpi_acceptance_26_cb_action_unresolved_plierror.c, built beside
// the run and named by vpi_acceptance_26_cb_action_unresolved_plierror.args, is
// the VPI application under test (#4338).
module top;
  initial begin
    #1 $probe;
    $nobody_registered_this;
  end
endmodule
