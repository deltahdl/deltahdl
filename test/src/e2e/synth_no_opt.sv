// --no-opt skips the optimization passes and reports the graph as lowered: the
// five AND nodes of the two chains, against the three that synth_balance_shares
// reports once Balance has made the outputs share.
module synth_no_opt(input logic a, b, c, d, output logic y1, y2);
  assign y1 = ((a & b) & c) & d;
  assign y2 = (a & b) & (c & d);
endmodule
