// §16.13.1 Multiclocked sequences: differently clocked subsequences are
// concatenated by ##1, which moves to the nearest strictly subsequent tick
// of the second clock, or by ##0, which moves to the nearest possibly
// overlapping one, and by no other sequence operator; and each maximal
// singly clocked subsequence shall admit only nonempty matches, since an
// empty one would leave the clock of the join ambiguous. The clause's
// illegal examples are written first, sig1[*0:1] after a change of clock,
// ##2 between differently clocked subsequences and intersect over them,
// and are reported; the two legal joins after them are not, nor is a
// clock named again after a delay, which is no change. The evaluation of
// the legal forms is test/src/e2e/multiclock_sequences.sv.
module multiclock_sequence_rules;
  logic clk0, clk1, clk2, sig0, sig1, s1, s2;

  assert property (@(posedge clk0) sig0 ##1 @(posedge clk1) sig1[*0:1]);
  assert property (@(posedge clk1) s1 ##2 @(posedge clk2) s2);
  assert property (@(posedge clk1) s1 intersect @(posedge clk2) s2);

  assert property (@(posedge clk0) sig0 ##1 @(posedge clk1) sig1);
  assert property (@(posedge clk0) sig0 ##0 @(posedge clk1) sig1);
  assert property (@(posedge clk1) s1 ##2 @(posedge clk1) s2);
endmodule
