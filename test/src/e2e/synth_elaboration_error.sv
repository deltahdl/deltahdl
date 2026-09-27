// A design the elaborator rejects is not synthesized: the error is reported and
// the run exits 1 with no synthesis summary.
module synth_elaboration_error(input logic a, output logic y);
  assign y = undeclared_z;
endmodule
