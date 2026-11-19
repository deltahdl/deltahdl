#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
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

std::string ToggleCount(const std::string& check, const std::string& stimulus,
                        char before, bool negative) {
  std::string body = stimulus;
  const char kAfter = before == '0' ? '1' : '0';
  body.replace(body.find('@'), 1, 1, kAfter);
  SimFixture f;
  f.ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions(
      {negative, false});
  return PreprocessAndCapture(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d = 0, output reg e = 0);\n"
      "  reg c = " +
          std::string(1, before) +
          "; reg n = 0; integer cnt = 0;\n"
          "  specify\n"
          "    " +
          check +
          "\n"
          "  endspecify\n"
          "  always @(n) cnt = cnt + 1;\n"
          "  initial begin\n"
          "    " +
          body +
          "\n"
          "    #50 $display(\"%0d\", cnt);\n"
          "  end\n"
          "endmodule\n",
      f);
}

std::string CountsAcrossTheFlip(const std::string& check,
                                const std::string& stimulus,
                                bool negative = false) {
  return ToggleCount(check, stimulus, '0', negative) +
         ToggleCount(check, stimulus, '1', negative);
}

constexpr const char* kTimestampChosenAtTheFirst = "0\n1\n";
constexpr const char* kChosenAtTheSecond = "1\n0\n";

constexpr const char* kSetupSide = "#100 d = 1; #1 c = @; #1 clk = 1;";
constexpr const char* kHoldSide = "#100 clk = 1; #1 c = @; #1 d = 1;";
constexpr const char* kRecoverySide = "#100 clk = 1; #2 c = @; #3 d = 1;";
constexpr const char* kRemovalSide = "#95 d = 1; #2 c = @; #3 clk = 1;";
constexpr const char* kDelayedReferenceFirst =
    "#100 clk = 1; #13 c = @; #2 d = 1;";
constexpr const char* kDelayedDataFirst = "#85 d = 1; #13 c = @; #2 clk = 1;";

TEST(SetupholdConditionPairing, TimestampFollowsTheDataOnTheSetupSide) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, 5, 5, n, c);",
                                kSetupSide),
            kTimestampChosenAtTheFirst);
}

TEST(SetupholdConditionPairing, TimecheckFollowsTheReferenceOnSetup) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, 5, 5, n, , c);",
                                kSetupSide),
            kChosenAtTheSecond);
}

TEST(SetupholdConditionPairing, TimestampFollowsTheReferenceOnTheHoldSide) {
  EXPECT_EQ(
      CountsAcrossTheFlip("$setuphold(posedge clk, d, 5, 5, n, c);", kHoldSide),
      kTimestampChosenAtTheFirst);
}

TEST(SetupholdConditionPairing, TimecheckFollowsTheDataOnTheHoldSide) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, 5, 5, n, , c);",
                                kHoldSide),
            kChosenAtTheSecond);
}

TEST(RecremConditionPairing, TimestampFollowsTheReferenceOnTheRecoverySide) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, 10, 10, n, c);",
                                kRecoverySide),
            kTimestampChosenAtTheFirst);
}

TEST(RecremConditionPairing, TimecheckFollowsTheDataOnRecovery) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, 10, 10, n, , c);",
                                kRecoverySide),
            kChosenAtTheSecond);
}

TEST(RecremConditionPairing, TimestampFollowsTheDataOnTheRemovalSide) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, 10, 10, n, c);",
                                kRemovalSide),
            kTimestampChosenAtTheFirst);
}

TEST(RecremConditionPairing, TimecheckFollowsTheReferenceOnRemoval) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, 10, 10, n, , c);",
                                kRemovalSide),
            kChosenAtTheSecond);
}

TEST(NegativeConditionPairing, NegativeSetupTimestampFollowsTheReference) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, -10, 20, n, c);",
                                kDelayedReferenceFirst, true),
            kTimestampChosenAtTheFirst);
}

TEST(NegativeConditionPairing, NegativeSetupTimecheckFollowsTheData) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, -10, 20, n, , c);",
                                kDelayedReferenceFirst, true),
            kChosenAtTheSecond);
}

TEST(NegativeConditionPairing, NegativeHoldTimestampFollowsTheData) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, 20, -10, n, c);",
                                kDelayedDataFirst, true),
            kTimestampChosenAtTheFirst);
}

TEST(NegativeConditionPairing, NegativeHoldTimecheckFollowsReference) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, 20, -10, n, , c);",
                                kDelayedDataFirst, true),
            kChosenAtTheSecond);
}

TEST(NegativeConditionPairing, NegativeRecoveryTimestampFollowsTheData) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, -10, 20, n, c);",
                                kDelayedDataFirst, true),
            kTimestampChosenAtTheFirst);
}

TEST(NegativeConditionPairing, NegativeRecoveryTimecheckFollowsTheReference) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, -10, 20, n, , c);",
                                kDelayedDataFirst, true),
            kChosenAtTheSecond);
}

TEST(NegativeConditionPairing, NegativeRemovalTimestampFollowsTheReference) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, 20, -10, n, c);",
                                kDelayedReferenceFirst, true),
            kTimestampChosenAtTheFirst);
}

TEST(NegativeConditionPairing, NegativeRemovalTimecheckFollowsTheData) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, 20, -10, n, , c);",
                                kDelayedReferenceFirst, true),
            kChosenAtTheSecond);
}

constexpr const char* kFlipBeforeTheDelayedReference =
    "#100 clk = 1; #5 c = @; #10 d = 1;";
constexpr const char* kFlipBeforeTheDelayedData =
    "#85 d = 1; #5 c = @; #10 clk = 1;";

TEST(UndelayedConditionSignals,
     DISABLED_TimestampIsReadWhenTheDelayedReferenceRises) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, -10, 20, n, c);",
                                kFlipBeforeTheDelayedReference, true),
            kChosenAtTheSecond);
}

TEST(UndelayedConditionSignals,
     DISABLED_TimestampIsReadWhenTheDelayedDataChanges) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, 20, -10, n, c);",
                                kFlipBeforeTheDelayedData, true),
            kChosenAtTheSecond);
}

TEST(UndelayedConditionSignals,
     DISABLED_RecremTimestampIsReadWhenTheDelayedReferenceRises) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, 20, -10, n, c);",
                                kFlipBeforeTheDelayedReference, true),
            kChosenAtTheSecond);
}

TEST(UndelayedConditionSignals,
     DISABLED_RecremTimestampIsReadWhenTheDelayedDataChanges) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, -10, 20, n, c);",
                                kFlipBeforeTheDelayedData, true),
            kChosenAtTheSecond);
}

constexpr const char* kFlipBeforeTheDelayedClockEnds =
    "#100 clk = 1; #5 e = 1; #3 c = @;";

TEST(UndelayedConditionSignals,
     DISABLED_TimecheckIsReadWhenTheDelayedReferenceRises) {
  EXPECT_EQ(CountsAcrossTheFlip("$setuphold(posedge clk, d, -10, 20); "
                                "$setuphold(posedge clk, e, -4, 8, n, , c);",
                                kFlipBeforeTheDelayedClockEnds, true),
            kChosenAtTheSecond);
}

TEST(UndelayedConditionSignals,
     DISABLED_RecremTimecheckIsReadWhenTheDelayedReferenceRises) {
  EXPECT_EQ(CountsAcrossTheFlip("$recrem(posedge clk, d, 20, -10); "
                                "$recrem(posedge clk, e, 8, -4, n, , c);",
                                kFlipBeforeTheDelayedClockEnds, true),
            kChosenAtTheSecond);
}

std::string ConditionsFromDelayedSignals(const std::string& te_init,
                                         const std::string& before_d) {
  SimFixture f;
  f.ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions({true, false});
  return PreprocessAndCapture(
      "`timescale 1ns/10ps\n"
      "module top(output reg CP = 0, output reg D = 0, output reg TI = 0,\n"
      "           output reg TE = " +
          te_init +
          ");\n"
          "  reg nd = 0, nt = 0, ne = 0;\n"
          "  wire dCP, dD, dTI, dTE;\n"
          "  assign TE_cond_D = (dTE !== 1'b1);\n"
          "  assign TE_cond_TI = (dTE !== 1'b0);\n"
          "  assign DXTI_cond = (dTI !== dD);\n"
          "  specify\n"
          "    $setuphold(posedge CP, D, -10, 20, nd, , TE_cond_D, dCP, dD);\n"
          "    $setuphold(posedge CP, TI, 20, -10, nt, , TE_cond_TI, dCP, "
          "dTI);\n"
          "    $setuphold(posedge CP, TE, -4, 8, ne, , DXTI_cond, dCP, dTE);\n"
          "  endspecify\n"
          "  always @(nd) $display(\"D %0.2f\", $realtime);\n"
          "  always @(nt) $display(\"TI %0.2f\", $realtime);\n"
          "  initial begin\n"
          "    #100 CP = 1; " +
          before_d +
          " D = 1;\n"
          "    #85 CP = 0; #85 TI = 1; #15 CP = 1;\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(UndelayedConditionSignals, ConditionsOfTheDelayedSignalsGateTheChecks) {
  EXPECT_EQ(ConditionsFromDelayedSignals("0", "#15"), "D 115.00\n");
  EXPECT_EQ(ConditionsFromDelayedSignals("1", "#15"), "TI 310.01\n");
}

TEST(UndelayedConditionSignals, ConditionOfADelayedSignalChangesLate) {
  EXPECT_EQ(ConditionsFromDelayedSignals("0", "#13 TE = 1; #2"),
            "D 115.00\nTI 310.01\n");
}

}  // namespace
