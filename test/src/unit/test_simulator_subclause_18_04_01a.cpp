#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <cstdlib>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

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
  EXPECT_LT(repeats, kSamples / 50);
}

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

  EXPECT_LT(std::abs(lower - upper), kSamples / 10);
  double mean = sum / kSamples;
  EXPECT_NEAR(mean, 1.0, 0.05);
}

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
      "    static C o = new;\n"
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

TEST(RandModifierUniformFromSource, RandSpansItsDeclaredRange) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int saw_lo, saw_hi, ok, i;\n"
      "    static C o = new;\n"
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
      "    static C o = new;\n"
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

TEST(RandModifierUniformFromSource, RandLogicTypeIsUniformOverRange) {
  const char* src =
      "class C;\n"
      "  rand logic [3:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int lo, hi, in_range, saw_lo, saw_hi, ok, i;\n"
      "    static C o = new;\n"
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

TEST(RandModifierUniformFromSource, RandWideIntegralIsUniformOverFullRange) {
  const char* src =
      "class C;\n"
      "  rand bit [15:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int lo, hi, in_range, saw_lo, saw_hi, ok, i;\n"
      "    static C o = new;\n"
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
      "    static B o = new;\n"
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

TEST(RandModifierSignedRange, SignedMemberReachesNegativeValues) {
  const char* src =
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int ok, i;\n"
      "    static C o = new;\n"
      "    good = 0;\n"
      "    for (i = 0; i < 200; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.x < 0) good = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

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
      "    static C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.x >= 0) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

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
      "    static C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.b >= -100 || o.b < -128) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

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
      "    static Outer o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.inner.x >= 0) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

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
      "    static C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.y <= 250 || o.y > 255) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandModifierUnsignedRange, SixtyFourBitDeclaredRangeReachesAllOnes) {
  RandVariable v;
  v.name = "v";
  v.width = 64;
  v.is_signed = false;
  v.BindDomainToDeclaredRange();

  EXPECT_EQ(static_cast<uint64_t>(v.min_val), 0u);
  EXPECT_EQ(static_cast<uint64_t>(v.max_val), UINT64_MAX);
  EXPECT_EQ(v.DomainSize(), UINT64_MAX);
}

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

TEST(RandModifierUnsignedRange, MemberReachesTheUpperHalfOfItsRange) {
  const char* src =
      "class C;\n"
      "  rand bit [63:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i, ok, saw_hi;\n"
      "    static C o = new;\n"
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
      "    static C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 50; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.x <= 64'h8000_0000_0000_0000) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandModifierUnsignedRange, RandTimeReachesTheUpperHalfOfItsRange) {
  const char* src =
      "class C;\n"
      "  rand time x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i, ok, saw_hi;\n"
      "    static C o = new;\n"
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
      "    static C o = new;\n"
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
