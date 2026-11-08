module synth_balance_chain(input logic a, b, c, d, output logic y);
  assign y = ((a & b) & c) & d;
endmodule
