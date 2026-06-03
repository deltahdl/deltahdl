#include <gtest/gtest.h>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <unordered_map>
#include <unordered_set>

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

// 18.4.1: an unconstrained "rand bit [7:0]" is assigned a value in 0..255 with
// equal probability. Over many draws the solver shall cover the whole range and
// keep the two halves of the range equally likely.
TEST(RandModifierUniformDistribution, UnconstrainedIntegralIsUniformOverRange) {
  ConstraintSolver solver(1);
  RandVariable y;
  y.name = "y";
  y.qualifier = RandQualifier::kRand;
  y.min_val = 0;
  y.max_val = 255;
  solver.AddVariable(y);

  constexpr int kSamples = 51200;  // 200x the 256-value range
  std::unordered_set<int64_t> seen;
  int64_t low_half = 0;
  int64_t high_half = 0;
  double sum = 0.0;
  for (int i = 0; i < kSamples; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("y");
    ASSERT_GE(v, 0);
    ASSERT_LE(v, 255);
    seen.insert(v);
    if (v < 128) {
      ++low_half;
    } else {
      ++high_half;
    }
    sum += static_cast<double>(v);
  }

  // Equal probability across the range: every value occurs, and neither half of
  // the range dominates (a tolerant band keeps the deterministic-seed check
  // robust while still failing a non-uniform or truncated distribution).
  EXPECT_EQ(seen.size(), 256u);
  EXPECT_LT(std::abs(low_half - high_half), kSamples / 10);
  // The mean of a uniform draw over 0..255 sits near the midpoint 127.5.
  double mean = sum / kSamples;
  EXPECT_NEAR(mean, 127.5, 5.0);
}

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

// 18.4.1: "their range" is the variable's declared range, not a fixed 0-based
// span. Over a small non-zero-based range every value shall be reachable with
// roughly equal frequency.
TEST(RandModifierUniformDistribution, IntegralUniformOverNonZeroBasedRange) {
  ConstraintSolver solver(13);
  RandVariable k;
  k.name = "k";
  k.qualifier = RandQualifier::kRand;
  k.min_val = 10;
  k.max_val = 13;  // four admissible values: 10, 11, 12, 13
  solver.AddVariable(k);

  constexpr int kSamples = 8000;
  std::unordered_map<int64_t, int> counts;
  for (int i = 0; i < kSamples; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("k");
    ASSERT_GE(v, 10);
    ASSERT_LE(v, 13);
    ++counts[v];
  }

  // Every value occurs and none strays far from its 1/4 expected share.
  EXPECT_EQ(counts.size(), 4u);
  int expected = kSamples / 4;
  for (const auto& [val, n] : counts) {
    EXPECT_GT(n, expected / 2);
    EXPECT_LT(n, expected * 3 / 2);
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

}  // namespace
