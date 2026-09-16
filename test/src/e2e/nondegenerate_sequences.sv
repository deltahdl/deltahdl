// §16.12.22 Nondegeneracy: a sequence that admits no match, like the
// clause's 1'b1 intersect (1'b1 ##1 1'b1), whose operands can have no
// length in common, or that admits only empty matches, like its 1'b1[*0],
// is degenerate; one that admits a nonempty match is nondegenerate, and may
// admit an empty match too, like its a[*0:2]. A sequence used as a property
// shall be nondegenerate and admit no empty match; the antecedent of |->
// shall be nondegenerate; and the antecedent of |=> shall admit at least
// one match, though it may admit only empty ones. The first five
// assertions below break the restrictions in turn, and are reported; the
// three after them keep to them, and are not.
module nondegenerate_sequences;
  logic clk, a, b;

  sequence never;
    1'b1 intersect (1'b1 ##1 1'b1);
  endsequence

  assert property (@(posedge clk) 1'b1 intersect (1'b1 ##1 1'b1));
  assert property (@(posedge clk) 1'b1[*0]);
  assert property (@(posedge clk) a[*0:2]);
  assert property (@(posedge clk) 1'b1[*0] |-> b);
  assert property (@(posedge clk) a ##1 never |=> b);

  assert property (@(posedge clk) a[*0:2] |-> b);
  assert property (@(posedge clk) 1'b1[*0] |=> b);
  assert property (@(posedge clk) a and a[*2]);
endmodule
