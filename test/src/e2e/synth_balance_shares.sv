// Balancing y1 rebuilds it as (a & b) & (c & d), the node y2 already is, so
// both outputs come to share three AND nodes where the lowering built five.
// synth_no_opt runs the same design without the passes and reports ten nodes.
module synth_balance_shares(input logic a, b, c, d, output logic y1, y2);
  assign y1 = ((a & b) & c) & d;
  assign y2 = (a & b) & (c & d);
endmodule
