// --synth elaborates the design, lowers its top-level module to an and-inverter
// graph, runs the optimization passes over it and reports the graph's size:
// two inputs and one output for a single AND gate.
module synth_and(input logic a, b, output logic y);
  assign y = a & b;
endmodule
