#include <gtest/gtest.h>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

// 18.4.1 "Rand modifier": variables declared rand are standard random
// variables whose values are uniformly distributed over their range. For an
// unconstrained integral rand variable, every value in the declared range is
// equally probable (so, e.g., the chance of a value repeating on successive
// randomize() calls is the reciprocal of the range size). For a rand real
// variable, the value is uniformly distributed over its range, meaning two
// equal-width subranges are equally likely. These tests observe the constraint
// solver applying that uniform distribution at the simulator stage.

using namespace delta;

namespace {

// 18.4.1: with each value equally probable across a 256-value range, the chance
// of the same value repeating on two successive randomize() calls is small
// (about 1/256). Immediate repeats shall therefore be rare, not the norm.
TEST(RandModifierUniformDistribution, RepeatOnSuccessiveCallsIsRare) {
  ConstraintSolver solver(7);
  RandVariable y;
  y.name = "y";
  y.min_val = 0;
  y.max_val = 255;
  solver.AddVariable(y);

  constexpr int kSamples = 25600;
  int64_t repeats = 0;
  ASSERT_TRUE(solver.Solve());
  int64_t prev = solver.GetValue("y");
  for (int i = 1; i < kSamples; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t cur = solver.GetValue("y");
    if (cur == prev) ++repeats;
    prev = cur;
  }
  // The expected repeat fraction is ~1/256; allow generous headroom but still
  // require it to be far below a non-uniform "frequently repeats" outcome.
  EXPECT_LT(repeats, kSamples / 50);
}

// 18.4.1 edge case: a zero-width integral range (min == max) admits a single
// value, so every draw shall return it. This exercises the same uniform
// integral path over a one-point domain.
TEST(RandModifierUniformDistribution, IntegralDegenerateRangeYieldsSoleValue) {
  ConstraintSolver solver(9);
  RandVariable k;
  k.name = "k";
  k.qualifier = RandQualifier::kRand;
  k.min_val = 42;
  k.max_val = 42;
  solver.AddVariable(k);

  for (int i = 0; i < 50; ++i) {
    ASSERT_TRUE(solver.Solve());
    EXPECT_EQ(solver.GetValue("k"), 42);
  }
}

// 18.4.1: a rand real variable's value is uniformly distributed over its range.
// For the range 0.0..2.0 the probability of landing in 0.0..1.0 shall equal the
// probability of landing in 1.0..2.0.
TEST(RandModifierUniformDistribution, RealValueIsUniformAcrossEqualSubranges) {
  ConstraintSolver solver(3);
  RandVariable v;
  v.name = "v";
  v.qualifier = RandQualifier::kRand;
  v.is_real = true;
  v.real_min = 0.0;
  v.real_max = 2.0;
  solver.AddVariable(v);

  constexpr int kSamples = 40000;
  int64_t lower = 0;
  int64_t upper = 0;
  double sum = 0.0;
  for (int i = 0; i < kSamples; ++i) {
    ASSERT_TRUE(solver.Solve());
    double v_val = solver.GetRealValue("v");
    ASSERT_GE(v_val, 0.0);
    ASSERT_LT(v_val, 2.0);
    if (v_val < 1.0) {
      ++lower;
    } else {
      ++upper;
    }
    sum += v_val;
  }

  // Equal-width subranges are equally likely under a uniform density.
  EXPECT_LT(std::abs(lower - upper), kSamples / 10);
  // A uniform draw over 0.0..2.0 has mean near the midpoint 1.0.
  double mean = sum / kSamples;
  EXPECT_NEAR(mean, 1.0, 0.05);
}

// 18.4.1: uniformity means the real value spreads across its whole range rather
// than clustering; the observed extremes shall approach both bounds.
TEST(RandModifierUniformDistribution, RealValueSpansItsRange) {
  ConstraintSolver solver(11);
  RandVariable v;
  v.name = "v";
  v.is_real = true;
  v.real_min = 0.0;
  v.real_max = 2.0;
  solver.AddVariable(v);

  double observed_min = 2.0;
  double observed_max = 0.0;
  for (int i = 0; i < 20000; ++i) {
    ASSERT_TRUE(solver.Solve());
    double v_val = solver.GetRealValue("v");
    observed_min = std::min(observed_min, v_val);
    observed_max = std::max(observed_max, v_val);
  }
  EXPECT_LT(observed_min, 0.05);
  EXPECT_GT(observed_max, 1.95);
}

// 18.4.1: a degenerate (non-positive-width) real range yields its lower bound
// deterministically rather than drawing from an empty interval.
TEST(RandModifierUniformDistribution, RealDegenerateRangeYieldsLowerBound) {
  ConstraintSolver solver(2);
  RandVariable v;
  v.name = "v";
  v.is_real = true;
  v.real_min = 1.5;
  v.real_max = 1.5;
  solver.AddVariable(v);

  ASSERT_TRUE(solver.Solve());
  EXPECT_DOUBLE_EQ(solver.GetRealValue("v"), 1.5);
}

// 18.4.1 edge case: a rand real range that straddles zero stays uniform, so the
// negative and positive halves are equally likely.
TEST(RandModifierUniformDistribution, RealUniformOverRangeStraddlingZero) {
  ConstraintSolver solver(17);
  RandVariable v;
  v.name = "v";
  v.is_real = true;
  v.real_min = -2.0;
  v.real_max = 2.0;
  solver.AddVariable(v);

  constexpr int kSamples = 40000;
  int64_t negative = 0;
  int64_t positive = 0;
  for (int i = 0; i < kSamples; ++i) {
    ASSERT_TRUE(solver.Solve());
    double x = solver.GetRealValue("v");
    ASSERT_GE(x, -2.0);
    ASSERT_LT(x, 2.0);
    if (x < 0.0) {
      ++negative;
    } else {
      ++positive;
    }
  }
  EXPECT_LT(std::abs(negative - positive), kSamples / 10);
}

// 18.4.1 (observed end to end from real source): a variable declared
// `rand bit [7:0]` is a standard random variable whose values are uniformly
// distributed over its declared 0..255 range — every value equally probable.
// Declaring it in a class and randomizing it many times drives the real
// production path: the rand modifier flows through eval_randomize into the
// uniform integral draw and each solved value is written back to the member.
// Over many draws neither half of the range dominates (each half takes roughly
// half of them) and every value stays inside 0..255 — the observable signature
// of an equal-probability draw across the whole range, as opposed to a biased
// or truncated one. Hand-building a RandVariable would not exercise the
// declaration-to-solver wiring that produces the range from the declared width.
TEST(RandModifierUniformFromSource,
     UnconstrainedRandIsUniformOverDeclaredRange) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int lo, hi, in_range, ok, i;\n"
      "    C o = new;\n"
      "    lo = 0; hi = 0; in_range = 1;\n"
      "    for (i = 0; i < 1024; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.y > 255) in_range = 0;\n"
      "      if (o.y < 128) lo = lo + 1; else hi = hi + 1;\n"
      "    end\n"
      "    good = (in_range && lo > 300 && hi > 300) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.1 (observed end to end): "uniformly distributed over their range" means
// the draw spans the full declared range rather than clustering. Across many
// randomize() calls on a `rand bit [7:0]` member both extremes are reached — a
// value under 16 and a value over 239 each appear — which a constant or narrow
// draw could not produce. This confirms the production randomize path spreads
// the value across the whole declared range.
TEST(RandModifierUniformFromSource, RandSpansItsDeclaredRange) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int saw_lo, saw_hi, ok, i;\n"
      "    C o = new;\n"
      "    saw_lo = 0; saw_hi = 0;\n"
      "    for (i = 0; i < 1024; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.y < 16) saw_lo = 1;\n"
      "      if (o.y > 239) saw_hi = 1;\n"
      "    end\n"
      "    good = (saw_lo && saw_hi) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.1 (observed end to end with a real §18.5 constraint): "their range" is
// the variable's effective admissible range, so when a genuine constraint block
// narrows a rand variable the uniform draw covers exactly that narrowed range.
// A `rand bit [7:0] y` bounded by a `constraint` block to 10..13 (the §18.5
// construct the rule consumes, parsed and elaborated from real syntax) is
// randomized many times: every draw lands in 10..13 and all four admissible
// values are reached with roughly even frequency — uniform over the effective
// range, not merely the declared width. This observes the production randomize
// path applying the uniform rule to a range produced by a real constraint
// rather than a hand-built domain.
TEST(RandModifierUniformFromSource, UniformOverConstrainedRange) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] y;\n"
      "  constraint c { y >= 10; y <= 13; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int c10, c11, c12, c13, in_range, ok, i;\n"
      "    C o = new;\n"
      "    c10 = 0; c11 = 0; c12 = 0; c13 = 0; in_range = 1;\n"
      "    for (i = 0; i < 4000; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.y < 10) in_range = 0;\n"
      "      if (o.y > 13) in_range = 0;\n"
      "      if (o.y == 10) c10 = c10 + 1;\n"
      "      if (o.y == 11) c11 = c11 + 1;\n"
      "      if (o.y == 12) c12 = c12 + 1;\n"
      "      if (o.y == 13) c13 = c13 + 1;\n"
      "    end\n"
      "    good = (in_range &&\n"
      "            c10 > 500 && c11 > 500 && c12 > 500 && c13 > 500) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.1 (observed end to end, 4-state integral operand form): the uniform rule
// applies to any integral rand variable, not only 2-state `bit`. A
// `rand logic [3:0]` member ranges over 0..15; randomizing it many times drives
// the real production path with a 4-state, narrower declared type. Both halves
// of the range are populated roughly evenly, both extreme values (0 and 15) are
// reached, and every draw stays inside 0..15 — the equal-probability signature
// over the whole range for a differently typed integral operand.
TEST(RandModifierUniformFromSource, RandLogicTypeIsUniformOverRange) {
  const char* src =
      "class C;\n"
      "  rand logic [3:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int lo, hi, in_range, saw_lo, saw_hi, ok, i;\n"
      "    C o = new;\n"
      "    lo = 0; hi = 0; in_range = 1; saw_lo = 0; saw_hi = 0;\n"
      "    for (i = 0; i < 2000; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.y > 15) in_range = 0;\n"
      "      if (o.y < 8) lo = lo + 1; else hi = hi + 1;\n"
      "      if (o.y == 0) saw_lo = 1;\n"
      "      if (o.y == 15) saw_hi = 1;\n"
      "    end\n"
      "    good = (in_range && lo > 600 && hi > 600 &&\n"
      "            saw_lo && saw_hi) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.1 (observed end to end, wider integral operand form): "their range" is
// the full declared range, so a wider integral member is uniform over its whole
// span. A `rand bit [15:0]` (range 0..65535) randomized many times spreads
// evenly across the two halves of the 16-bit range and reaches both extremes,
// with every draw in range. This exercises the
// uniform rule over a materially larger declared range than the 8-bit form,
// confirming the production path does not clamp the distribution to a fixed
// sub-span.
TEST(RandModifierUniformFromSource, RandWideIntegralIsUniformOverFullRange) {
  const char* src =
      "class C;\n"
      "  rand bit [15:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int lo, hi, in_range, saw_lo, saw_hi, ok, i;\n"
      "    C o = new;\n"
      "    lo = 0; hi = 0; in_range = 1; saw_lo = 0; saw_hi = 0;\n"
      "    for (i = 0; i < 4096; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.y > 65535) in_range = 0;\n"
      "      if (o.y < 32768) lo = lo + 1; else hi = hi + 1;\n"
      "      if (o.y < 2048) saw_lo = 1;\n"
      "      if (o.y > 63487) saw_hi = 1;\n"
      "    end\n"
      "    good = (in_range && lo > 1500 && hi > 1500 &&\n"
      "            saw_lo && saw_hi) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
