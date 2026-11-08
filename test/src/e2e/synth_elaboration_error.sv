module synth_elaboration_error(input logic a, output logic y);
  assign y = undeclared_z;
endmodule
