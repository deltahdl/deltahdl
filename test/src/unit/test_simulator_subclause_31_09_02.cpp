#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

// §31.9.2: with positive setup and hold (Figure 31-4), the violation window
// straddles the reference edge and the condition applies to both signals.
TEST(NegativeTimingConditionRoles, TimestampBothNonNegativeIsBoth) {
  EXPECT_EQ(TimestampConditionRole(5, 10), NegativeTimingConditionRole::kBoth);
}

TEST(NegativeTimingConditionRoles, TimecheckBothNonNegativeIsBoth) {
  EXPECT_EQ(TimecheckConditionRole(5, 10), NegativeTimingConditionRole::kBoth);
}

// Degenerate guard: when neither limit is positive there is no first/second
// distinction to anchor an association to a single signal.
TEST(NegativeTimingConditionRoles, BothNegativeIsNone) {
  EXPECT_EQ(TimestampConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
  EXPECT_EQ(TimecheckConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
}

// §31.9.2: a negative setup makes the timecheck condition associate with the
// data signal (the one transitioning second) and the timestamp with the ref.
// A zero hold beside the negative setup also pins the strict `< 0` boundary
// (zero is non-negative, so the case still resolves as negative-setup).
TEST(NegativeTimingConditionRoles, NegativeSetupZeroHoldMatchesNegativeSetup) {
  EXPECT_EQ(TimestampConditionRole(-5, 0), NegativeTimingConditionRole::kRef);
  EXPECT_EQ(TimecheckConditionRole(-5, 0), NegativeTimingConditionRole::kData);
}

// §31.9.2: a negative hold makes the timecheck condition associate with the
// reference signal and the timestamp with the data; a zero setup pins the
// strict `< 0` boundary on the other operand.
TEST(NegativeTimingConditionRoles, ZeroSetupNegativeHoldMatchesNegativeHold) {
  EXPECT_EQ(TimestampConditionRole(0, -5), NegativeTimingConditionRole::kData);
  EXPECT_EQ(TimecheckConditionRole(0, -5), NegativeTimingConditionRole::kRef);
}

// §31.9.2: implicit delayed copies are made for the reference and data signals.
TEST(NegativeTimingConditionDelay, ReferenceAndDataOperandsGetDelayedCopies) {
  EXPECT_TRUE(
      OperandGetsImplicitDelayedCopy(TimingCheckOperandKind::kReference));
  EXPECT_TRUE(OperandGetsImplicitDelayedCopy(TimingCheckOperandKind::kData));
}

// §31.9.2: condition operands are never implicitly delayed by the simulator;
// a delayed condition must instead be built explicitly from delayed signals.
TEST(NegativeTimingConditionDelay, ConditionOperandsAreNotDelayed) {
  EXPECT_FALSE(OperandGetsImplicitDelayedCopy(
      TimingCheckOperandKind::kTimestampCondition));
  EXPECT_FALSE(OperandGetsImplicitDelayedCopy(
      TimingCheckOperandKind::kTimecheckCondition));
}

// §31.9.2 (printed page 922): `$setuphold(clk, data, tsetup, thold, ntfr, ,
// cond1)` is the pair `$setup(data, clk &&& cond1, ...)` and `$hold(clk,
// data &&& cond1, ...)`, the timecheck_condition gating whichever event
// transitions second. d rises 2 before clk at 12 while c1 is 0, which is no
// setup violation; d falls 2 before clk at 32 with c1 at 1, which is one.
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

// The timestamp_condition gates the event that transitions first: d's rise
// at 10 under c0 = 0 opens no setup window, d's fall at 30 under c0 = 1 does.
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

// On the hold side the reference edge transitions first, so the
// timecheck_condition gates the data transition after it: d changing 2 after
// clk at 10 while c1 is 0 is no hold violation, 2 after clk at 30 with c1 at 1
// is one.
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
