#include <cstdint>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §18.16: each randcase_item weight expression is evaluated at most once. A
// weight expression with a side effect (here a post-increment of a counter)
// must therefore advance that counter exactly once per branch -- once for the
// weight sum and the branch selection together, never twice. Three branches
// whose weights each bump `cnt` leave it at 3, not 6.
TEST(RandcaseWeightedCase, WeightExpressionsEvaluatedAtMostOnce) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned cnt;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    cnt = 0;\n"
      "    x = 0;\n"
      "    randcase\n"
      "      (cnt++ + 1) : x = 1;\n"
      "      (cnt++ + 1) : x = 2;\n"
      "      (cnt++ + 1) : x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // Each of the three weight expressions ran exactly once.
  EXPECT_EQ(f.ctx.FindVariable("cnt")->value.ToUint64(), 3u);
  // A branch was selected and its body executed.
  auto x = f.ctx.FindVariable("x")->value.ToUint64();
  EXPECT_GE(x, 1u);
  EXPECT_LE(x, 3u);
}

// §18.16: a zero-weight branch interleaved among nonzero ones is still skipped;
// the random number maps onto the nonzero branches in declaration order. Here
// only the third branch carries weight, so it is always selected.
TEST(RandcaseWeightedCase, SingleNonzeroWeightAmongZerosAlwaysSelected) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randcase\n"
      "      0 : x = 1;\n"
      "      0 : x = 2;\n"
      "      5 : x = 3;\n"
      "      0 : x = 4;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 3u);
}

// §18.16: if all randcase_items specify zero weights, no branch is taken and a
// warning can be issued. The target variable keeps its prior value and the
// simulator reports a warning.
TEST(RandcaseWeightedCase, AllZeroWeightsTakesNoBranchAndWarns) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    x = 99;\n"
      "    randcase\n"
      "      0 : x = 1;\n"
      "      0 : x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 99u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §18.16: the randcase weights can be arbitrary expressions, not just
// constants. The example mixes arithmetic, bitwise, and sized-literal weight
// expressions over module variables; the simulator evaluates them and selects
// one of the branches.
TEST(RandcaseWeightedCase, WeightsCanBeArbitraryExpressions) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a, b;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    a = 8'd6;\n"
      "    b = 8'd2;\n"
      "    x = 0;\n"
      "    randcase\n"
      "      a + b   : x = 1;\n"
      "      a - b   : x = 2;\n"
      "      a ^ ~b  : x = 3;\n"
      "      12'h800 : x = 4;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto x = f.ctx.FindVariable("x")->value.ToUint64();
  EXPECT_GE(x, 1u);
  EXPECT_LE(x, 4u);
}

// §18.16: each weight is summed and compared as an unsigned value. A signed
// narrow weight holding the bit pattern of a negative number (byte -1 == 0xFF)
// must therefore count as a large positive weight, not as a non-positive one.
// Paired with a zero-weight sibling, the unsigned branch is the only reachable
// one and is selected on every draw -- which holds only under unsigned
// summation and comparison.
TEST(RandcaseWeightedCase, NegativeSignedWeightCountsAsUnsigned) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte w;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    w = -1;\n"
      "    x = 0;\n"
      "    randcase\n"
      "      w : x = 7;\n"
      "      0 : x = 8;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 7u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §18.16: a branch's weight divided by the sum of all weights is the
// probability of taking that branch, and the random number maps onto the
// branches in declaration order. Over many iterations with weights {3, 1, 4}
// (sum 8) the observed branch frequencies track the 0.375 / 0.125 / 0.5
// probabilities, and every iteration selects exactly one branch.
TEST(RandcaseWeightedCase, BranchFrequenciesTrackWeightProbabilities) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned c1, c2, c3;\n"
      "  int i;\n"
      "  initial begin\n"
      "    c1 = 0; c2 = 0; c3 = 0;\n"
      "    for (i = 0; i < 8000; i = i + 1) begin\n"
      "      randcase\n"
      "        3 : c1 = c1 + 1;\n"
      "        1 : c2 = c2 + 1;\n"
      "        4 : c3 = c3 + 1;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto c1 = f.ctx.FindVariable("c1")->value.ToUint64();
  auto c2 = f.ctx.FindVariable("c2")->value.ToUint64();
  auto c3 = f.ctx.FindVariable("c3")->value.ToUint64();
  // Every iteration selects exactly one branch.
  EXPECT_EQ(c1 + c2 + c3, 8000u);
  // Frequencies are within a loose band of their expected probabilities.
  EXPECT_NEAR(static_cast<double>(c1) / 8000.0, 0.375, 0.05);
  EXPECT_NEAR(static_cast<double>(c2) / 8000.0, 0.125, 0.05);
  EXPECT_NEAR(static_cast<double>(c3) / 8000.0, 0.500, 0.05);
}

// §18.16: each randcase draw is a random number across the full [0, sum)
// range, even when the sum of the weights exceeds 32 bits -- which a single
// 32-bit draw cannot span. With two equal weights of 2**32 (sum 2**33), the
// upper branch occupies the half of the range at or above 2**32. It must still
// be reachable: a draw confined to the low 32 bits would never land there, so
// observing both branches selected proves the wider range is covered.
TEST(RandcaseWeightedCase, SumWiderThan32BitsCoversFullRange) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned lo_cnt, hi_cnt;\n"
      "  int i;\n"
      "  initial begin\n"
      "    lo_cnt = 0; hi_cnt = 0;\n"
      "    for (i = 0; i < 200; i = i + 1) begin\n"
      "      randcase\n"
      "        64'h100000000 : lo_cnt = lo_cnt + 1;\n"
      "        64'h100000000 : hi_cnt = hi_cnt + 1;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto lo_cnt = f.ctx.FindVariable("lo_cnt")->value.ToUint64();
  auto hi_cnt = f.ctx.FindVariable("hi_cnt")->value.ToUint64();
  // Every iteration selects exactly one branch.
  EXPECT_EQ(lo_cnt + hi_cnt, 200u);
  // The branch whose weight slot lies at/above 2**32 is reachable; a draw
  // limited to 32 bits would leave hi_cnt at zero.
  EXPECT_GT(hi_cnt, 0u);
  EXPECT_GT(lo_cnt, 0u);
}

}  // namespace
