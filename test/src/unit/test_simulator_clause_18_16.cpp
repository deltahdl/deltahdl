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

// §18.16: the precision of each weight expression is self-determined. Each
// weight is evaluated at its own bit length before the weights are summed, not
// at the sum's combined precision. `4'd8 + 4'd8` is a 4-bit self-determined
// addition, so its true result 16 wraps to 0 within four bits and that branch
// carries zero weight -- even though the wide sibling weight would give the sum
// ample precision to hold 16. A weight coerced to the sum's precision before
// evaluation would instead be 16 and reachable. Over many draws the narrow
// branch is never selected, which holds only when the weight keeps its own
// self-determined precision.
TEST(RandcaseWeightedCase, WeightPrecisionIsSelfDetermined) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned narrow_hits, wide_hits;\n"
      "  int i;\n"
      "  initial begin\n"
      "    narrow_hits = 0; wide_hits = 0;\n"
      "    for (i = 0; i < 500; i = i + 1) begin\n"
      "      randcase\n"
      "        (4'd8 + 4'd8) : narrow_hits = narrow_hits + 1;\n"
      "        32'd1000      : wide_hits = wide_hits + 1;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // The 4-bit self-determined addition wrapped to zero; that branch is
  // unreachable regardless of the wider sibling weight's precision.
  EXPECT_EQ(f.ctx.FindVariable("narrow_hits")->value.ToUint64(), 0u);
  // Every draw landed on the wide, nonzero branch.
  EXPECT_EQ(f.ctx.FindVariable("wide_hits")->value.ToUint64(), 500u);
  // A nonzero total weight means no all-zero warning was issued.
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §18.16: a branch weight may be produced by a named elaboration-time constant
// (a parameter), not only by an inline literal or a variable expression. A
// parameter reference resolves through a different path than an inline literal
// yet still supplies the branch weight. A nonzero parameter weight beside a
// zero-weight sibling is the only reachable branch, so it is selected on every
// draw -- observing that the parameter-produced value drives the selection.
TEST(RandcaseWeightedCase, ParameterValuedWeightIsUsed) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P_W = 5;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randcase\n"
      "      P_W : x = 1;\n"
      "      0   : x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 1u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §18.16: a weight may equally be a module-local named constant (a localparam),
// declared locally but resolved at elaboration. A nonzero localparam weight
// beside a zero sibling is always selected, confirming a localparam-produced
// value is accepted as a branch weight.
TEST(RandcaseWeightedCase, LocalparamValuedWeightIsUsed) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int L_W = 4;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randcase\n"
      "      L_W : x = 1;\n"
      "      0   : x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 1u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §18.16: randcase obtains its random number from the thread-stable
// $urandom_range() stream, so the selection sequence is governed by the current
// process's seedable RNG. Seeding that RNG through real source syntax
// (process::self().srandom, §18.14) and running a fixed run of randcase draws,
// then rewinding to the same seed, reproduces the identical selection sequence;
// a different seed produces a different one. This drives the process-srandom
// dependency through the full pipeline and shows the draws are consumed from
// the seedable stream, not from a seed-independent source. The per-iteration
// selection is folded into a running signature so a whole sequence, not just
// one draw, is compared.
TEST(RandcaseWeightedCase, SelectionDrawsFromSeedableUrandomStream) {
  const char* src =
      "module t;\n"
      "  int sig_a, sig_b, sig_c;\n"
      "  int i, sel;\n"
      "  initial begin\n"
      "    process pr = process::self();\n"
      "    pr.srandom(555);\n"
      "    sig_a = 0;\n"
      "    for (i = 0; i < 40; i = i + 1) begin\n"
      "      sel = 0;\n"
      "      randcase\n"
      "        1 : sel = 1;\n"
      "        2 : sel = 2;\n"
      "        3 : sel = 3;\n"
      "      endcase\n"
      "      sig_a = sig_a * 7 + sel;\n"
      "    end\n"
      "    pr.srandom(555);\n"
      "    sig_b = 0;\n"
      "    for (i = 0; i < 40; i = i + 1) begin\n"
      "      sel = 0;\n"
      "      randcase\n"
      "        1 : sel = 1;\n"
      "        2 : sel = 2;\n"
      "        3 : sel = 3;\n"
      "      endcase\n"
      "      sig_b = sig_b * 7 + sel;\n"
      "    end\n"
      "    pr.srandom(999);\n"
      "    sig_c = 0;\n"
      "    for (i = 0; i < 40; i = i + 1) begin\n"
      "      sel = 0;\n"
      "      randcase\n"
      "        1 : sel = 1;\n"
      "        2 : sel = 2;\n"
      "        3 : sel = 3;\n"
      "      endcase\n"
      "      sig_c = sig_c * 7 + sel;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto a = f.ctx.FindVariable("sig_a")->value.ToUint64();
  auto b = f.ctx.FindVariable("sig_b")->value.ToUint64();
  auto c = f.ctx.FindVariable("sig_c")->value.ToUint64();
  // Same seed rewinds the stream and reproduces the identical selection run.
  EXPECT_EQ(a, b);
  // A different seed drives a different run, so randcase truly consumes the
  // RNG.
  EXPECT_NE(a, c);
}

}  // namespace
