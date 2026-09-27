// --no-opt skips the optimization passes and reports the graph as lowered.
// For a single AND gate that is the same size as the optimized graph; see #4444
// for why a case cannot yet show the passes shrinking one.
module synth_and(input logic a, b, output logic y);
  assign y = a & b;
endmodule
