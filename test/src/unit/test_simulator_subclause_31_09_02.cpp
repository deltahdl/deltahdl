#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

TEST(NegativeTimingConditionRoles, TimestampBothNonNegativeIsBoth) {
  EXPECT_EQ(TimestampConditionRole(5, 10), NegativeTimingConditionRole::kBoth);
}

TEST(NegativeTimingConditionRoles, TimecheckBothNonNegativeIsBoth) {
  EXPECT_EQ(TimecheckConditionRole(5, 10), NegativeTimingConditionRole::kBoth);
}

TEST(NegativeTimingConditionRoles, BothNegativeIsNone) {
  EXPECT_EQ(TimestampConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
  EXPECT_EQ(TimecheckConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
}

TEST(NegativeTimingConditionRoles, NegativeSetupZeroHoldMatchesNegativeSetup) {
  EXPECT_EQ(TimestampConditionRole(-5, 0), NegativeTimingConditionRole::kRef);
  EXPECT_EQ(TimecheckConditionRole(-5, 0), NegativeTimingConditionRole::kData);
}

TEST(NegativeTimingConditionRoles, ZeroSetupNegativeHoldMatchesNegativeHold) {
  EXPECT_EQ(TimestampConditionRole(0, -5), NegativeTimingConditionRole::kData);
  EXPECT_EQ(TimecheckConditionRole(0, -5), NegativeTimingConditionRole::kRef);
}

TEST(NegativeTimingConditionDelay, ReferenceAndDataOperandsGetDelayedCopies) {
  EXPECT_TRUE(
      OperandGetsImplicitDelayedCopy(TimingCheckOperandKind::kReference));
  EXPECT_TRUE(OperandGetsImplicitDelayedCopy(TimingCheckOperandKind::kData));
}

TEST(NegativeTimingConditionDelay, ConditionOperandsAreNotDelayed) {
  EXPECT_FALSE(OperandGetsImplicitDelayedCopy(
      TimingCheckOperandKind::kTimestampCondition));
  EXPECT_FALSE(OperandGetsImplicitDelayedCopy(
      TimingCheckOperandKind::kTimecheckCondition));
}

TEST(SetupholdConditionsDriven, TimecheckConditionGatesTheSetupSide) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(\n"
                       "    output reg clk = 0,\n"
                       "    output reg d = 0);\n"
                       "  reg c1 = 0; reg n = 0; integer cnt = 0;\n"
                       "  specify\n"
                       "    $setuphold(posedge clk, d, 5, 5, n, , c1);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "  initial begin\n"
                       "    #10 d = 1; #2 clk = 1;\n"
                       "    #8 clk = 0; c1 = 1;\n"
                       "    #10 d = 0; #2 clk = 1;\n"
                       "    #5 $display(\"%0d\", cnt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

TEST(SetupholdConditionsDriven, TimestampConditionGatesTheSetupSide) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(\n"
                       "    output reg clk = 0,\n"
                       "    output reg d = 0);\n"
                       "  reg c0 = 0; reg n = 0; integer cnt = 0;\n"
                       "  specify\n"
                       "    $setuphold(posedge clk, d, 5, 5, n, c0);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "  initial begin\n"
                       "    #10 d = 1; #2 clk = 1;\n"
                       "    #8 clk = 0; c0 = 1;\n"
                       "    #10 d = 0; #2 clk = 1;\n"
                       "    #5 $display(\"%0d\", cnt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

TEST(SetupholdConditionsDriven, TimecheckConditionGatesTheHoldSide) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(\n"
                       "    output reg clk = 0,\n"
                       "    output reg d = 0);\n"
                       "  reg c1 = 0; reg n = 0; integer cnt = 0;\n"
                       "  specify\n"
                       "    $setuphold(posedge clk, d, 5, 5, n, , c1);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "  initial begin\n"
                       "    #10 clk = 1; #2 d = 1;\n"
                       "    #8 clk = 0; c1 = 1;\n"
                       "    #10 clk = 1; #2 d = 0;\n"
                       "    #5 $display(\"%0d\", cnt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

}  // namespace
