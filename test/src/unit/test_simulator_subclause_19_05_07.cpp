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

CoverpointEffectiveType Unsigned(uint32_t width) { return {width, false}; }
CoverpointEffectiveType Signed(uint32_t width) { return {width, true}; }

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

TEST(ValueResolution, StaticCastToEffectiveType) {
  EXPECT_EQ(CoverageDB::CastToEffectiveType(15, Unsigned(3)), 7);
  EXPECT_EQ(CoverageDB::CastToEffectiveType(7, Signed(3)), -1);
  EXPECT_EQ(CoverageDB::CastToEffectiveType(15, Signed(3)), -1);
  EXPECT_EQ(CoverageDB::CastToEffectiveType(3, Signed(3)), 3);
  EXPECT_EQ(CoverageDB::CastToEffectiveType(-1, Signed(3)), -1);
}

TEST(ValueResolution, UnsignedEffectiveTypeWarnsOnNegativeSignedValue) {
  EXPECT_EQ(CoverageDB::ResolveBinValue(-1, true, false, false, Unsigned(3)),
            BinValueResolution::kUnsignedNegative);
  EXPECT_EQ(CoverageDB::ResolveBinValue(-1, true, false, false, Signed(3)),
            BinValueResolution::kOk);
}

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

TEST(ValueResolution, UnknownBitsWarnExceptForWildcardBins) {
  EXPECT_EQ(CoverageDB::ResolveBinValue(3, false, true, false, Unsigned(3)),
            BinValueResolution::kUnknownBits);
  EXPECT_EQ(CoverageDB::ResolveBinValue(3, false, true, true, Unsigned(3)),
            BinValueResolution::kOk);
}

TEST(ValueResolution, WarnedSingletonDoesNotParticipate) {
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(BinValueResolution::kOk));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      BinValueResolution::kUnsignedNegative));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      BinValueResolution::kValueChanged));
  EXPECT_FALSE(
      CoverageDB::SingletonValueParticipates(BinValueResolution::kUnknownBits));
}

TEST(ValueResolution, RangeDropsWhenEndpointUnknownOrAllValuesWarn) {
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({2, 5, false, true, false}, Unsigned(3))
          .empty());
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({6, 10, false, false, false}, Signed(3))
          .empty());
}

TEST(ValueResolution, RangeBecomesIntersectionWithEffectiveDomain) {
  EXPECT_EQ(
      CoverageDB::ResolveBinRange({6, 10, false, false, false}, Unsigned(3)),
      (std::vector<int64_t>{6, 7}));
  EXPECT_EQ(
      CoverageDB::ResolveBinRange({1, 10, false, false, false}, Unsigned(3)),
      (std::vector<int64_t>{1, 2, 3, 4, 5, 6, 7}));
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, false, false}, Signed(3)),
            (std::vector<int64_t>{2, 3}));
}

TEST(ValueResolution, UnsignedThreeBitBinClampsTheRangePastSeven) {
  CoverpointEffectiveType eff = Unsigned(3);
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(1, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, false, false}, eff),
            (std::vector<int64_t>{2, 3, 4, 5}));
  EXPECT_EQ(CoverageDB::ResolveBinRange({6, 10, false, false, false}, eff),
            (std::vector<int64_t>{6, 7}));
}

TEST(ValueResolution,
     UnsignedThreeBitBinDropsMinusOneAndFifteenAndClampsItsRange) {
  CoverpointEffectiveType eff = Unsigned(3);
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(-1, true, false, false, eff)));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(15, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({1, 10, false, false, false}, eff),
            (std::vector<int64_t>{1, 2, 3, 4, 5, 6, 7}));
}

TEST(ValueResolution,
     SignedThreeBitBinClampsOneRangeAndDropsTheRangeAboveThree) {
  CoverpointEffectiveType eff = Signed(3);
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(1, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, false, false}, eff),
            (std::vector<int64_t>{2, 3}));
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({6, 10, false, false, false}, eff).empty());
}

TEST(ValueResolution, SignedThreeBitBinKeepsMinusOneAndDropsFifteen) {
  CoverpointEffectiveType eff = Signed(3);
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(-1, true, false, false, eff)));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(15, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({1, 10, false, false, false}, eff),
            (std::vector<int64_t>{1, 2, 3}));
}

TEST(ValueResolution, WildcardRangeEndpointDoesNotDropRange) {
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({2, 5, false, true, false}, Unsigned(3))
          .empty());
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, true, true}, Unsigned(3)),
            (std::vector<int64_t>{2, 3, 4, 5}));
}

TEST(ValueResolution, ExpressibleDomainBoundsByEffectiveType) {
  EXPECT_EQ(CoverageDB::EffectiveTypeMin(Unsigned(3)), 0);
  EXPECT_EQ(CoverageDB::EffectiveTypeMax(Unsigned(3)), 7);
  EXPECT_EQ(CoverageDB::EffectiveTypeMin(Signed(3)), -4);
  EXPECT_EQ(CoverageDB::EffectiveTypeMax(Signed(3)), 3);
}

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
