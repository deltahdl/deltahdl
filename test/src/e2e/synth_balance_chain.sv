// Balancing the chain rebuilds it as (a & b) & (c & d), which is as many AND
// nodes as the chain had. The count is of the nodes the outputs still reach, so
// the two the rebuilt chain left behind are not reported.
module synth_balance_chain(input logic a, b, c, d, output logic y);
  assign y = ((a & b) & c) & d;
endmodule
