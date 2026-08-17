#include <gtest/gtest.h>

#include <algorithm>
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

// 18.4.1: a rand variable is uniformly distributed over the range its
// declared type admits -- the clause's own example calls rand bit [7:0] "an
// 8-bit unsigned integer with a range of 0 to 255" and requires an
// unconstrained one to be assigned a value in that range. The value drawn from
// that range is what the constraints are solved against. A solver that drew
// from a wider domain and only truncated on write-back would satisfy the
// clause's stated observables -- the committed value would still be uniform
// over the declared range -- while every constraint saw a number the variable
// cannot hold. This makes that difference observable: 's -> d == 0' relates a
// 1-bit s to a 2-bit d, so it holds for five of the eight value combinations
// and randomize() shall succeed on every call. Drawn from a wider domain the
// same relation demands an exactly-zero d while a nonzero s is near-certain,
// so it becomes unsatisfiable in practice and randomize() fails. The relation
// is not of the foldable variable-against-constant shape, so it is evaluated
// against the drawn values themselves rather than seeded, which is what makes
// the domain visible here. The second read confirms the solved pairs are
// legal, so a wider domain cannot be traded for a wrong answer.
TEST(RandModifierUniformFromSource,
     NarrowRandVariablesSolvedWithinDeclaredRange) {
  const char* src =
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [1:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int allok;\n"
      "  int legal;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    allok = 1;\n"
      "    legal = 1;\n"
      "    for (int i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) allok = 0;\n"
      "      if (o.s == 1 && o.d != 0) legal = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
  EXPECT_EQ(RunAndGet(src, "legal"), 1u);
}

// 18.4.1 requires a rand variable's values to be uniformly distributed over
// "their range", and 6.11.3 fixes what that range is: byte, shortint, int,
// integer and longint default to signed, so a w-bit one spans -2**(w-1) to
// 2**(w-1)-1 and half of it is negative. The tests below observe the negative
// half being reachable on each of the three paths that build a solver domain --
// a class randomize(), a scope std::randomize(), and the joint solve a rand
// object handle produces -- because the domain is bound in a separate place on
// each and a range correct on one says nothing about the other two.
//
// The unconstrained observation is the weaker of the two forms. std::randomize
// writes back into a variable that is itself signed, so a draw with the top bit
// set reads back negative there whether or not the draw was ever negative; only
// a constraint that no non-negative value can satisfy separates the two.

// 18.4.1 / 6.11.3: `rand integer` is a 32-bit signed variable, so a draw
// uniform over its range reaches the negative half. Over 200 unconstrained
// randomize() calls a negative value shall appear -- from a non-negative domain
// none ever can, and from the signed range the chance of missing is 2**-200.
TEST(RandModifierSignedRange, SignedMemberReachesNegativeValues) {
  const char* src =
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int ok, i;\n"
      "    C o = new;\n"
      "    good = 0;\n"
      "    for (i = 0; i < 200; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.x < 0) good = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.1 / 6.11.3: a constraint admits every value of the variable's range that
// satisfies it, and half a signed variable's range is negative, so `x < 0` on a
// `rand integer` is satisfiable and randomize() shall report success. A domain
// starting at zero leaves it with no solution at all, which is the failure this
// separates from a merely skewed distribution.
TEST(RandModifierSignedRange, NegativeRequiringConstraintIsSatisfiable) {
  const char* src =
      "class C;\n"
      "  rand integer x;\n"
      "  constraint c { x < 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i;\n"
      "    C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.x >= 0) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.1 / 6.11.3: the low end of the range is -2**(w-1), so an 8-bit signed
// `rand byte` constrained below -100 draws from -128..-101 and nothing outside
// it. This pins the lower bound rather than only the sign: a domain that
// admitted negatives but stopped short of -128 would satisfy the test above and
// fail this one.
TEST(RandModifierSignedRange, SignedByteDrawsWithinItsDeclaredLowerBound) {
  const char* src =
      "class C;\n"
      "  rand byte b;\n"
      "  constraint c { b < -100; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i;\n"
      "    C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.b >= -100 || o.b < -128) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 6.11.3: min_val and max_val are signed integers, so a caller that writes a
// negative bound and never declares a signedness means the negative number it
// spells. Signed is therefore what an undeclared signedness reads the domain
// in. Read unsigned, -10 is a value far above 10: the range [-10, 10] comes out
// inverted and empty instead of the twenty-one values it names, and a solve
// over it collapses onto the bound rather than drawing from between them.
TEST(RandModifierSignedRange,
     UndeclaredSignednessReadsANegativeBoundAsNegative) {
  RandVariable v;
  v.name = "v";
  v.width = 8;
  v.min_val = -10;
  v.max_val = 10;

  EXPECT_TRUE(v.DomainLess(v.min_val, v.max_val));
  EXPECT_EQ(v.DomainSize(), 21u);
}

// 18.4.1 / 6.11.3 through the 18.12 scope path: std::randomize() names ordinary
// scope variables as its random variables, and an `int` is signed, so an inline
// constraint requiring a negative value is satisfiable there too. This path
// builds its domain in its own place, from the target variable rather than from
// a declared member type.
TEST(RandModifierSignedRange, ScopeRandomizeSolvesNegativeConstraint) {
  const char* src =
      "module t;\n"
      "  int good;\n"
      "  int a;\n"
      "  initial begin\n"
      "    int i;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (std::randomize(a) with { a < 0; } == 0) good = 0;\n"
      "      if (a >= 0) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.1 / 6.11.3 through the 18.5.8 joint path: a rand object handle pulls the
// referenced object's random variables into one joint solve, and a member's
// declared signedness has to survive being renamed into that joint table. The
// path is entered only when the active random object set holds more than the
// root object, so the nested object is built in a constructor to put it there.
TEST(RandModifierSignedRange, JointSolveSolvesNegativeConstraint) {
  const char* src =
      "class Inner;\n"
      "  rand integer x;\n"
      "  constraint c { x < 0; }\n"
      "endclass\n"
      "class Outer;\n"
      "  rand Inner inner;\n"
      "  function new();\n"
      "    inner = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i;\n"
      "    Outer o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.inner.x >= 0) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 6.11.3 puts bit, reg, logic and time on unsigned, so the range of a
// `rand bit [7:0]` is still 0..255 with no negative half. Deriving the domain
// from the declared signedness has to leave the unsigned types where they were,
// which a constraint no value of an unsigned range can satisfy shows: it is
// unsatisfiable, and randomize() reports failure rather than success.
TEST(RandModifierSignedRange, UnsignedMemberKeepsItsNonNegativeRange) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] y;\n"
      "  constraint c { y > 250; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i;\n"
      "    C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.y <= 250 || o.y > 255) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.1 requires a rand variable's values to be uniformly distributed over
// "their range", and reads a declaration as naming that range: `rand bit [7:0]`
// is "an 8-bit unsigned integer with a range of 0 to 255". 6.11.3 puts bit,
// reg, logic and time on unsigned, so a 64-bit one of those spans 0 to 2**64-1.
// That top is one value beyond what an int64_t counts up to, and a bound held
// as a signed number can only stop at 2**63-1 -- half the declared range, and
// the half a constraint requiring a large value needs. The tests below pin the
// whole range: the bound the declared type produces, the order that bound is
// read in, and the draws and constraint solutions that follow from both.

// 18.4.1 / 6.11.3: an unsigned 64-bit type spans 0 to 2**64-1, so that is the
// domain its declaration binds. The top of the range is all ones, which is the
// value 2**64-1 of the declared type and the bit pattern -1 of the int64_t
// holding it; a bound that stopped at the largest positive int64_t would leave
// the upper half of the declared range outside the domain.
TEST(RandModifierUnsignedRange, SixtyFourBitDeclaredRangeReachesAllOnes) {
  RandVariable v;
  v.name = "v";
  v.width = 64;
  v.is_signed = false;
  v.BindDomainToDeclaredRange();

  EXPECT_EQ(static_cast<uint64_t>(v.min_val), 0u);
  EXPECT_EQ(static_cast<uint64_t>(v.max_val), UINT64_MAX);
  // 2**64 values have no exact 64-bit count, so the size saturates.
  EXPECT_EQ(v.DomainSize(), UINT64_MAX);
}

// 18.4.1 / 6.11.3: the width below the widest is where a signed bound is still
// exact -- an unsigned 63-bit type spans 0 to 2**63-1, the largest value an
// int64_t holds -- so widening the 64-bit case must not spill into it. A domain
// of all ones here would admit values the declared type cannot hold.
TEST(RandModifierUnsignedRange,
     SixtyThreeBitDeclaredRangeStopsAtSignedMaximum) {
  RandVariable v;
  v.name = "v";
  v.width = 63;
  v.is_signed = false;
  v.BindDomainToDeclaredRange();

  EXPECT_EQ(v.min_val, 0);
  EXPECT_EQ(static_cast<uint64_t>(v.max_val), (uint64_t{1} << 63) - 1);
  EXPECT_EQ(v.DomainSize(), uint64_t{1} << 63);
}

// 18.4.1 / 6.11.3: the range an unsigned declaration names runs upward from 0
// to its top, so every value in it is above the bottom. The top of a 64-bit
// unsigned range has its high bit set, which the built-in signed operators read
// as a number below zero: ordered that way the range is inverted and empty,
// which is what puts its upper half out of reach. The declared order is the
// type's own.
TEST(RandModifierUnsignedRange, DeclaredOrderPutsTheTopOfTheRangeAboveZero) {
  RandVariable v;
  v.name = "v";
  v.width = 64;
  v.is_signed = false;
  v.BindDomainToDeclaredRange();

  EXPECT_TRUE(v.DomainLess(v.min_val, v.max_val));
  EXPECT_FALSE(v.DomainLess(v.max_val, v.min_val));
  EXPECT_EQ(v.DomainMax(v.min_val, v.max_val), v.max_val);
  EXPECT_EQ(v.DomainMin(v.min_val, v.max_val), v.min_val);
}

// 18.5: the collapse that guards the solver against a domain with no value in
// it judges emptiness in the declared order too. The top of a full unsigned
// 64-bit range has its high bit set, so read as a signed number it lies below
// the bottom: collapsed on that reading, the whole range becomes the single
// value 0 and nothing the domain was widened for survives to be drawn.
TEST(RandModifierUnsignedRange, EmptyDomainCollapseLeavesAFullRangeWhole) {
  RandVariable v;
  v.name = "v";
  v.width = 64;
  v.is_signed = false;
  v.BindDomainToDeclaredRange();
  v.CollapseEmptyDomain();

  EXPECT_EQ(static_cast<uint64_t>(v.min_val), 0u);
  EXPECT_EQ(static_cast<uint64_t>(v.max_val), UINT64_MAX);
}

// 18.5: a domain whose bounds really are inverted -- opposing bounds folded out
// of the constraints, with no value left between them -- still collapses onto
// its lower bound, so the solver is handed a range holding one value rather
// than none.
TEST(RandModifierUnsignedRange, InvertedDomainCollapsesOntoItsLowerBound) {
  RandVariable v;
  v.name = "v";
  v.width = 8;
  v.is_signed = false;
  v.min_val = 200;
  v.max_val = 100;
  v.CollapseEmptyDomain();

  EXPECT_EQ(v.min_val, 200);
  EXPECT_EQ(v.max_val, 200);
}

// 18.4.1: an unconstrained rand variable "shall be assigned any value in the
// range ... with equal probability", so both halves of a 64-bit unsigned range
// are drawn. Over 200 draws from the whole range the chance of never setting
// the high bit is 2**-200; from a domain capped at 2**63-1 it never can be set.
TEST(RandModifierUnsignedRange, SolverDrawsAboveTheSignedMaximum) {
  ConstraintSolver solver(11);
  RandVariable v;
  v.name = "v";
  v.width = 64;
  v.is_signed = false;
  v.BindDomainToDeclaredRange();
  solver.AddVariable(v);

  bool saw_upper_half = false;
  for (int i = 0; i < 200; ++i) {
    ASSERT_TRUE(solver.Solve());
    if ((static_cast<uint64_t>(solver.GetValue("v")) >> 63) != 0)
      saw_upper_half = true;
  }
  EXPECT_TRUE(saw_upper_half);
}

// 18.4.1 / 6.11.3 observed end to end: `rand bit [63:0]` declares a range of 0
// to 2**64-1, and an unconstrained member of that type reaches the half of it
// above 2**63-1. Drawn from a domain that stops at the largest positive
// int64_t, no call ever does.
TEST(RandModifierUnsignedRange, MemberReachesTheUpperHalfOfItsRange) {
  const char* src =
      "class C;\n"
      "  rand bit [63:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i, ok, saw_hi;\n"
      "    C o = new;\n"
      "    saw_hi = 0;\n"
      "    for (i = 0; i < 200; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.x >= 64'h8000_0000_0000_0000) saw_hi = 1;\n"
      "    end\n"
      "    good = saw_hi;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.1: the values of a rand variable are distributed over its range, so a
// constraint naming a value in that range has a solution. This is the
// consequence that bites: with the domain capped at 2**63-1 a constraint
// requiring a larger value has no value left to satisfy it, and randomize()
// reports failure on a constraint the declared range admits.
TEST(RandModifierUnsignedRange, UpperHalfRequiringConstraintIsSatisfiable) {
  const char* src =
      "class C;\n"
      "  rand bit [63:0] x;\n"
      "  constraint c { x > 64'h8000_0000_0000_0000; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i;\n"
      "    C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.x <= 64'h8000_0000_0000_0000) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 6.11.3 names time among the types that default to unsigned, and it is 64 bits
// wide, so `rand time` declares the same 0 to 2**64-1 range as `rand bit
// [63:0]` and reaches the same upper half. The range follows from the declared
// type, not from the syntax a width was written in.
TEST(RandModifierUnsignedRange, RandTimeReachesTheUpperHalfOfItsRange) {
  const char* src =
      "class C;\n"
      "  rand time x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i, ok, saw_hi;\n"
      "    C o = new;\n"
      "    saw_hi = 0;\n"
      "    for (i = 0; i < 200; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.x >= 64'h8000_0000_0000_0000) saw_hi = 1;\n"
      "    end\n"
      "    good = saw_hi;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 6.11.3 puts longint on signed, so a 64-bit signed range runs from -2**63 to
// 2**63-1 and a constraint requiring a negative value is satisfiable. Reading
// every 64-bit range as unsigned would order that range's negative half above
// its positive half and leave `x < 0` with nothing to draw.
TEST(RandModifierUnsignedRange, SignedLongintKeepsItsNegativeHalf) {
  const char* src =
      "class C;\n"
      "  rand longint x;\n"
      "  constraint c { x < 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i;\n"
      "    C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.x >= 0) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
