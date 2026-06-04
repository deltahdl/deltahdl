#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §18.17.1 claim 1: the probability of selecting a production list is
// proportional to its specified weight. With weights 3:1 over many trials the
// heavier alternative is generated substantially more often, while both remain
// reachable.
TEST(RandsequenceSim, ProbabilityProportionalToWeight) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] na, nb;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0; nb = 0;\n"
      "    for (i = 0; i < 200; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : a := 3 | b := 1;\n"
      "        a : { na = na + 1; };\n"
      "        b : { nb = nb + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* na = f.ctx.FindVariable("na");
  auto* nb = f.ctx.FindVariable("nb");
  ASSERT_NE(na, nullptr);
  ASSERT_NE(nb, nullptr);

  // Every trial picks exactly one alternative.
  EXPECT_EQ(na->value.ToUint64() + nb->value.ToUint64(), 200u);
  // Both alternatives are reachable, and the weight-3 list dominates the
  // weight-1 list (expected 150 vs 50).
  EXPECT_GT(na->value.ToUint64(), 0u);
  EXPECT_GT(nb->value.ToUint64(), 0u);
  EXPECT_GT(na->value.ToUint64(), nb->value.ToUint64());
}

// §18.17.1 claim 1 (extreme): a production list whose weight evaluates to zero
// is never generated; selection probability proportional to weight makes a
// zero weight unreachable.
TEST(RandsequenceSim, ZeroWeightProductionListNeverSelected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] na, nb;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0; nb = 0;\n"
      "    for (i = 0; i < 50; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : a := 0 | b := 1;\n"
      "        a : { na = na + 1; };\n"
      "        b : { nb = nb + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* na = f.ctx.FindVariable("na");
  auto* nb = f.ctx.FindVariable("nb");
  ASSERT_NE(na, nullptr);
  ASSERT_NE(nb, nullptr);

  EXPECT_EQ(na->value.ToUint64(), 0u);
  EXPECT_EQ(nb->value.ToUint64(), 50u);
}

// §18.17.1 claims 6 & 7: a production list with no specified weight uses a
// weight of 1. Here 'a' has no weight (defaults to 1) and 'b' is given weight
// 0, so 'a' is always selected — demonstrating the unspecified weight is the
// nonzero default of 1 rather than 0.
TEST(RandsequenceSim, UnspecifiedWeightDefaultsToOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] na, nb;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0; nb = 0;\n"
      "    for (i = 0; i < 50; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : a | b := 0;\n"
      "        a : { na = na + 1; };\n"
      "        b : { nb = nb + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* na = f.ctx.FindVariable("na");
  auto* nb = f.ctx.FindVariable("nb");
  ASSERT_NE(na, nullptr);
  ASSERT_NE(nb, nullptr);

  EXPECT_EQ(na->value.ToUint64(), 50u);
  EXPECT_EQ(nb->value.ToUint64(), 0u);
}

// §18.17.1 claims 2, 3 & 5: the ':=' weight may be an expression that evaluates
// to an integral value, and the weight is evaluated when its enclosing
// production is selected (allowing weights to change dynamically). The same
// grammar shape yields different selections because the weight expression reads
// the current value of 'g': with g=1 the first list wins, with g=0 the second.
TEST(RandsequenceSim, WeightEvaluatedDynamicallyFromExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic g;\n"
      "  logic [7:0] x1, x2;\n"
      "  initial begin\n"
      "    g = 1'b1;\n"
      "    randsequence(m1)\n"
      "      m1 : p := g | q := (1'b1 - g);\n"
      "      p : { x1 = 8'd1; };\n"
      "      q : { x1 = 8'd2; };\n"
      "    endsequence\n"
      "    g = 1'b0;\n"
      "    randsequence(m2)\n"
      "      m2 : r := g | s := (1'b1 - g);\n"
      "      r : { x2 = 8'd1; };\n"
      "      s : { x2 = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x1 = f.ctx.FindVariable("x1");
  auto* x2 = f.ctx.FindVariable("x2");
  ASSERT_NE(x1, nullptr);
  ASSERT_NE(x2, nullptr);

  // g=1: weights are 1 vs 0 -> first list 'p'.
  EXPECT_EQ(x1->value.ToUint64(), 1u);
  // g=0: weights are 0 vs 1 -> second list 's'.
  EXPECT_EQ(x2->value.ToUint64(), 2u);
}

// §18.17.1 claims 6 & 7: the unspecified weight is not merely nonzero — it is
// exactly 1. Pitting an unspecified alternative against an explicit weight of 3
// yields an effective 1:3 split, so the explicit list is generated about three
// times as often. The expected counts (~50 vs ~150) make nb exceed twice na,
// which would fail if the default were 2 or larger (~80 vs ~120), pinning the
// implied default to 1.
TEST(RandsequenceSim, DefaultWeightOfOneRelativeToExplicit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] na, nb;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0; nb = 0;\n"
      "    for (i = 0; i < 200; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : a | b := 3;\n"
      "        a : { na = na + 1; };\n"
      "        b : { nb = nb + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* na = f.ctx.FindVariable("na");
  auto* nb = f.ctx.FindVariable("nb");
  ASSERT_NE(na, nullptr);
  ASSERT_NE(nb, nullptr);

  EXPECT_EQ(na->value.ToUint64() + nb->value.ToUint64(), 200u);
  EXPECT_GT(na->value.ToUint64(), 0u);
  EXPECT_GT(nb->value.ToUint64(), 0u);
  // 1:3 split -> nb is roughly triple na, comfortably above 2x.
  EXPECT_GT(nb->value.ToUint64(), 2u * na->value.ToUint64());
}

// §18.17.1 claim 5 (edge case): a weight is only meaningful when assigned to
// alternative production lists separated by '|'. A production with a single
// list has no alternatives, so its weight is inconsequential — even a weight of
// 0, which would make a list unreachable when competing against alternatives
// (see ZeroWeightProductionListNeverSelected), leaves the lone list generated
// every time. This exercises the single-list short circuit in SelectRule, which
// returns the only list before the weight is consulted.
TEST(RandsequenceSim, WeightOnNonAlternativeProductionIsIgnored) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] na;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0;\n"
      "    for (i = 0; i < 50; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : a := 0;\n"
      "        a : { na = na + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* na = f.ctx.FindVariable("na");
  ASSERT_NE(na, nullptr);

  // Despite the zero weight, the sole production list is always generated.
  EXPECT_EQ(na->value.ToUint64(), 50u);
}

}  // namespace
