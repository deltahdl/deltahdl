#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

// Effective type helpers used across the value-resolution tests.
CoverpointEffectiveType Unsigned(uint32_t width) { return {width, false}; }
CoverpointEffectiveType Signed(uint32_t width) { return {width, true}; }

// LRM 19.5.7 a: with no coverpoint type the effective type of e is its
// self-determined type; with a coverpoint type it is that type.
TEST(ValueResolution, EffectiveTypeSelectsCoverpointTypeWhenPresent) {
  CoverpointEffectiveType self = Signed(8);
  CoverpointEffectiveType cp_type = Unsigned(3);

  CoverpointEffectiveType no_type =
      CoverageDB::EffectiveCoverpointType(false, cp_type, self);
  EXPECT_EQ(no_type.width, 8u);
  EXPECT_TRUE(no_type.is_signed);

  CoverpointEffectiveType with_type =
      CoverageDB::EffectiveCoverpointType(true, cp_type, self);
  EXPECT_EQ(with_type.width, 3u);
  EXPECT_FALSE(with_type.is_signed);
}

// LRM 19.5.7 b: a bin value is statically cast to the effective type — reduced
// to its width and reinterpreted with the type's signedness.
TEST(ValueResolution, StaticCastToEffectiveType) {
  // 15 does not fit bit[2:0]; the cast keeps the low 3 bits -> 7.
  EXPECT_EQ(CoverageDB::CastToEffectiveType(15, Unsigned(3)), 7);
  // For a signed 3-bit type the high bit is a sign bit: 7 -> -1, 15 -> -1.
  EXPECT_EQ(CoverageDB::CastToEffectiveType(7, Signed(3)), -1);
  EXPECT_EQ(CoverageDB::CastToEffectiveType(15, Signed(3)), -1);
  // An in-range value is unchanged.
  EXPECT_EQ(CoverageDB::CastToEffectiveType(3, Signed(3)), 3);
  EXPECT_EQ(CoverageDB::CastToEffectiveType(-1, Signed(3)), -1);
}

// LRM 19.5.7 b, condition 1: an unsigned effective type with a negative signed
// bin value warns.
TEST(ValueResolution, UnsignedEffectiveTypeWarnsOnNegativeSignedValue) {
  EXPECT_EQ(CoverageDB::ResolveBinValue(-1, /*value_is_signed=*/true,
                                        /*value_has_xz=*/false,
                                        /*is_wildcard=*/false, Unsigned(3)),
            BinValueResolution::kUnsignedNegative);
  // A negative value is fine for a signed effective type that can hold it.
  EXPECT_EQ(CoverageDB::ResolveBinValue(-1, true, false, false, Signed(3)),
            BinValueResolution::kOk);
}

// LRM 19.5.7 b, condition 2: a value the effective type cannot express warns
// because the cast changes it under the rules for ==, which compare signed
// only where both sides are (LRM 11.8.1). An unsigned 5 on a signed 3-bit
// type casts to -3, whose bits 101 compare equal to it unsigned, so it fits;
// a signed 5 does not, nor does an unsigned 9, whose bits exceed the width.
TEST(ValueResolution, OutOfRangeValueWarnsBecauseCastChangesIt) {
  EXPECT_EQ(CoverageDB::ResolveBinValue(15, false, false, false, Unsigned(3)),
            BinValueResolution::kValueChanged);
  EXPECT_EQ(CoverageDB::ResolveBinValue(5, false, false, false, Signed(3)),
            BinValueResolution::kOk);
  EXPECT_EQ(CoverageDB::ResolveBinValue(5, true, false, false, Signed(3)),
            BinValueResolution::kValueChanged);
  EXPECT_EQ(CoverageDB::ResolveBinValue(9, false, false, false, Signed(3)),
            BinValueResolution::kValueChanged);
  EXPECT_EQ(CoverageDB::ResolveBinValue(3, false, false, false, Unsigned(3)),
            BinValueResolution::kOk);
}

// LRM 19.5.7 b, condition 3 and the wildcard preamble: a value with x/z bits
// warns, except for a wildcard bin whose unknown bits are treated as 0/1.
TEST(ValueResolution, UnknownBitsWarnExceptForWildcardBins) {
  EXPECT_EQ(CoverageDB::ResolveBinValue(3, false, /*value_has_xz=*/true,
                                        /*is_wildcard=*/false, Unsigned(3)),
            BinValueResolution::kUnknownBits);
  EXPECT_EQ(CoverageDB::ResolveBinValue(3, false, /*value_has_xz=*/true,
                                        /*is_wildcard=*/true, Unsigned(3)),
            BinValueResolution::kOk);
}

// LRM 19.5.7, first warning bullet: a singleton value that warns does not
// participate in the bin.
TEST(ValueResolution, WarnedSingletonDoesNotParticipate) {
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(BinValueResolution::kOk));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      BinValueResolution::kUnsignedNegative));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      BinValueResolution::kValueChanged));
  EXPECT_FALSE(
      CoverageDB::SingletonValueParticipates(BinValueResolution::kUnknownBits));
}

// LRM 19.5.7, second range bullet: a range whose endpoint carries x/z bits, or
// whose values would all warn, drops out entirely.
TEST(ValueResolution, RangeDropsWhenEndpointUnknownOrAllValuesWarn) {
  // x/z endpoint removes the range (non-wildcard).
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({/*low=*/2, /*high=*/5, /*low_has_xz=*/false,
                                   /*high_has_xz=*/true, /*is_wildcard=*/false},
                                  Unsigned(3))
          .empty());
  // [6:10] under signed bit[2:0] (domain -4..3) has no expressible value.
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({6, 10, false, false, false}, Signed(3))
          .empty());
}

// LRM 19.5.7, third range bullet: a range with at least one non-warning value
// becomes the intersection of its values with the effective type's domain.
TEST(ValueResolution, RangeBecomesIntersectionWithEffectiveDomain) {
  // [6:10] under bit[2:0] (0..7) -> [6:7].
  EXPECT_EQ(
      CoverageDB::ResolveBinRange({6, 10, false, false, false}, Unsigned(3)),
      (std::vector<int64_t>{6, 7}));
  // [1:10] under bit[2:0] (0..7) -> [1:7].
  EXPECT_EQ(
      CoverageDB::ResolveBinRange({1, 10, false, false, false}, Unsigned(3)),
      (std::vector<int64_t>{1, 2, 3, 4, 5, 6, 7}));
  // [2:5] under signed bit[2:0] (-4..3) -> [2:3].
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, false, false}, Signed(3)),
            (std::vector<int64_t>{2, 3}));
}

// LRM 19.5.7 worked example b1: bit[2:0] p1, bins b1 = {1,[2:5],[6:10]} is
// resolved to {1,[2:5],[6:7]} (the [6:10] range warns and is clamped).
TEST(ValueResolution, ExampleB1UnsignedThreeBit) {
  CoverpointEffectiveType eff = Unsigned(3);
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(1, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, false, false}, eff),
            (std::vector<int64_t>{2, 3, 4, 5}));
  EXPECT_EQ(CoverageDB::ResolveBinRange({6, 10, false, false, false}, eff),
            (std::vector<int64_t>{6, 7}));
}

// LRM 19.5.7 worked example b2: bit[2:0] p1, bins b2 = {-1,[1:10],15} is
// resolved to {[1:7]} (the -1 and 15 singletons warn out, [1:10] clamps).
TEST(ValueResolution, ExampleB2UnsignedThreeBit) {
  CoverpointEffectiveType eff = Unsigned(3);
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(-1, true, false, false, eff)));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(15, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({1, 10, false, false, false}, eff),
            (std::vector<int64_t>{1, 2, 3, 4, 5, 6, 7}));
}

// LRM 19.5.7 worked example b3: bit signed [2:0] p2, bins b3 = {1,[2:5],[6:10]}
// is resolved to {1,[2:3]} ([6:10] warns out, [2:5] clamps).
TEST(ValueResolution, ExampleB3SignedThreeBit) {
  CoverpointEffectiveType eff = Signed(3);
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(1, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, false, false}, eff),
            (std::vector<int64_t>{2, 3}));
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({6, 10, false, false, false}, eff).empty());
}

// LRM 19.5.7 worked example b4: bit signed [2:0] p2, bins b4 = {-1,[1:10],15}
// is resolved to {-1,[1:3]} (-1 survives, 15 warns out, [1:10] clamps).
TEST(ValueResolution, ExampleB4SignedThreeBit) {
  CoverpointEffectiveType eff = Signed(3);
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(-1, true, false, false, eff)));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(15, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({1, 10, false, false, false}, eff),
            (std::vector<int64_t>{1, 2, 3}));
}

// LRM 19.5.7, second range bullet (wildcard exception): an x/z bit in a range
// endpoint drops the range for an ordinary bin, but for a wildcard bin the
// unknown bits are resolved to 0/1 beforehand, so the range survives and
// clamps to the effective type's domain instead of dropping out.
TEST(ValueResolution, WildcardRangeEndpointDoesNotDropRange) {
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({/*low=*/2, /*high=*/5, /*low_has_xz=*/false,
                                   /*high_has_xz=*/true, /*is_wildcard=*/false},
                                  Unsigned(3))
          .empty());
  EXPECT_EQ(
      CoverageDB::ResolveBinRange({/*low=*/2, /*high=*/5, /*low_has_xz=*/false,
                                   /*high_has_xz=*/true, /*is_wildcard=*/true},
                                  Unsigned(3)),
      (std::vector<int64_t>{2, 3, 4, 5}));
}

// LRM 19.5.7, third range bullet: the values expressible by the effective type
// form the closed domain a surviving range intersects with — an unsigned type
// starts at zero, a signed type spans its two's-complement range.
TEST(ValueResolution, ExpressibleDomainBoundsByEffectiveType) {
  EXPECT_EQ(CoverageDB::EffectiveTypeMin(Unsigned(3)), 0);
  EXPECT_EQ(CoverageDB::EffectiveTypeMax(Unsigned(3)), 7);
  EXPECT_EQ(CoverageDB::EffectiveTypeMin(Signed(3)), -4);
  EXPECT_EQ(CoverageDB::EffectiveTypeMax(Signed(3)), 3);
}

// LRM 19.5.7: a singleton the coverpoint's type cannot express, `-1` and
// `15` on bit [2:0] or one holding x, takes no part in its bin, a range keeps
// only the values the type expresses, and a bin left with none is out of
// coverage: b2, b3 and bx go, and the array b1[] over [6:10] is b1[6], b1[7].
TEST(CovergroupInstanceSim, BinValuesTheTypeCannotExpressLeaveTheBin) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module top;\n"
                "  bit [2:0] p1; bit signed [2:0] p2; logic [3:0] p3;\n"
                "  covergroup cg;\n"
                "    a: coverpoint p1 { bins b2 = {-1, 15}; bins ok = {3}; }\n"
                "    b: coverpoint p2 { bins b3 = {[6:10]}; bins ok = {0}; }\n"
                "    e: coverpoint p1 { bins b1[] = {[6:10]}; }\n"
                "    d: coverpoint p3 { bins bx = {4'b11x0}; bins ok = {3}; }\n"
                "  endgroup\n"
                "  cg c = new;\n"
                "  initial begin\n"
                "    p1 = 3; p2 = 0; p3 = 3; c.sample(); p1 = 7; c.sample();\n"
                "    $display(\"%0.2f %0.2f %0.2f %0.2f\",\n"
                "      c.a.get_inst_coverage(), c.b.get_inst_coverage(),\n"
                "      c.e.get_inst_coverage(), c.d.get_inst_coverage());\n"
                "  end\n"
                "endmodule\n",
                f),
            "100.00 100.00 50.00 100.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// LRM 19.5.7: an implementation warns of a bin value the effective type
// cannot express, as for the clause's own b2 and b4 of `{-1, [1:10], 15}`,
// and of one holding x or z, except in a wildcard bin.
TEST(CovergroupInstanceSim, BinValuesTheTypeCannotExpressDrawAWarning) {
  SimFixture f;
  RunCapture(
      "module top;\n"
      "  bit [2:0] p1; bit signed [2:0] p2; logic [3:0] p3;\n"
      "  covergroup cg;\n"
      "    a: coverpoint p1 { bins b2 = {-1, [1:10], 15}; }\n"
      "    b: coverpoint p2 { bins b4 = {-1, [1:10], 15};\n"
      "      bins b3 = {[6:10]}; }\n"
      "    c: coverpoint p3 { bins bx = {4'b11x0};\n"
      "      wildcard bins w = {4'b11x0}; bins rx = {[4'b00x0:4'b0011]}; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial $display(\"done\");\n"
      "endmodule\n",
      f);
  for (auto [line, message] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {4u,
            "bin value -1 is negative while the coverpoint's type is "
            "unsigned, and takes no part in its bin"},
           {4u,
            "bin range [1:10] holds values the coverpoint's type cannot "
            "express; only [1:7] takes part in its bin"},
           {4u,
            "bin value 15 does not fit the coverpoint's type and takes no "
            "part in its bin"},
           {5u,
            "bin range [1:10] holds values the coverpoint's type cannot "
            "express; only [1:3] takes part in its bin"},
           {5u,
            "bin value 15 does not fit the coverpoint's type and takes no "
            "part in its bin"},
           {6u,
            "bin range [6:10] holds no value the coverpoint's type can "
            "express and takes no part in its bin"},
           {7u, "a bin value holding x or z bits takes no part in its bin"}}) {
    EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), message, line, "19.5.7"));
  }
  EXPECT_EQ(f.diag.WarningCount(), 8u);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// LRM 19.5.7 with 11.8.1: an unsigned bin value or range on a signed
// coverpoint compares unsigned, so the values whose bits fit the type take
// part, each as the type holds it: 3'b111 is -1, [3'd4:3'd6] is -4 to -2 and
// [3'd2:3'd5] is 2 to 3 with -4 to -3, all hit by the samples -1 and -3, with
// no warning.
TEST(CovergroupInstanceSim, UnsignedBinValuesOnASignedTypeTakeTheirCastValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit signed [2:0] p2;\n"
                 "  covergroup cg;\n"
                 "    a: coverpoint p2 { bins neg = {3'b111};\n"
                 "      bins up = {[3'd4:3'd6]}; bins st = {[3'd2:3'd5]}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    p2 = -1; c.sample(); p2 = -3; c.sample();\n"
                 "    $display(\"%0.2f\", c.a.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "100.00\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// LRM 19.5.7: each element of a set_covergroup_expression is a bin value like
// any other, so -1 and 9 of vals, which bit [2:0] cannot express, draw a
// warning and define no bin, leaving s[1] alone.
TEST(CovergroupInstanceSim, SetExpressionElementsTheTypeCannotExpressLeave) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [2:0] x; int n, t;\n"
                       "  int vals[] = '{1, -1, 9};\n"
                       "  covergroup cg;\n"
                       "    a: coverpoint x { bins s[] = vals; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    x = 1; c.sample();\n"
                       "    void'(c.a.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 t=1\n");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bin value -1 is negative while the coverpoint's "
                              "type is unsigned, and takes no part in its bin",
                              5, "19.5.7"));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bin value 9 does not fit the coverpoint's type "
                              "and takes no part in its bin",
                              5, "19.5.7"));
  EXPECT_EQ(f.diag.WarningCount(), 2u);
}

// LRM 11.4.13: a range whose low bound exceeds its high bound holds no value,
// so `[5:2]` gives rev none and leaves it out of coverage, with no LRM 19.5.7
// warning, as it holds no value to resolve; `[$:2]` reaches down to the type's
// least value, 0, and is hit by 1 as ok is.
TEST(CovergroupInstanceSim, ReversedBinRangeHoldsNoValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [2:0] x;\n"
          "  covergroup cg;\n"
          "    a: coverpoint x { bins rev = {[5:2]}; bins low = {[$:2]};\n"
          "      bins ok = {1}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    x = 1; c.sample();\n"
          "    $display(\"%0.2f\", c.a.get_inst_coverage());\n"
          "  end\n"
          "endmodule\n",
          f),
      "100.00\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// LRM 19.5.7: a 64-bit coverpoint expresses every value a bin value of 64 bits
// holds, so -1 and the largest longint stay in their bins with no warning.
TEST(CovergroupInstanceSim, SixtyFourBitCoverpointKeepsEveryBinValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  longint l;\n"
                       "  covergroup cg;\n"
                       "    a: coverpoint l { bins neg = {-1};\n"
                       "      bins big = {64'sh7fff_ffff_ffff_ffff}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    l = -1; c.sample();\n"
                       "    $display(\"%0.2f\", c.a.get_inst_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "50.00\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
