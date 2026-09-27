// --dump-aig prints the graph's size on a line of its own before the synthesis
// summary.
module synth_and(input logic a, b, output logic y);
  assign y = a & b;
endmodule
