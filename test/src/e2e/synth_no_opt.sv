module synth_no_opt(input logic a, b, c, d, output logic y1, y2);
  assign y1 = ((a & b) & c) & d;
  assign y2 = (a & b) & (c & d);
endmodule
