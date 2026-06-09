#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SystemTimingCheckSim, FullskewEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kFullskew;
  tc.ref_signal = "clk1";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "clk2";
  tc.data_edge = SpecifyEdge::kNegedge;
  tc.limit = 4;
  tc.limit2 = 6;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(stored.ref_signal, "clk1");
  EXPECT_EQ(stored.data_signal, "clk2");
  EXPECT_EQ(stored.limit, 4u);
  EXPECT_EQ(stored.limit2, 6u);
}

TEST(TimingCheckCommandSim, FullskewWithFlagsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr, 1, 0);\n"
      "  endspecify\n"
      "  initial x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TimingCheckEntry MakeFullskew(uint64_t limit1, uint64_t limit2) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kFullskew;
  tc.ref_signal = "clk1";
  tc.data_signal = "clk2";
  tc.limit = limit1;
  tc.limit2 = limit2;
  return tc;
}

TEST(FullskewTimingCheckWindow, DataBeyondLimit1Violates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_TRUE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 105));
}

TEST(FullskewTimingCheckWindow, DataAtLimit1DoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 104));
}

TEST(FullskewTimingCheckWindow, ReferenceBeyondLimit2Violates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_TRUE(mgr.CheckFullskewViolation("clk1", 107, "clk2", 100));
}

TEST(FullskewTimingCheckWindow, ReferenceAtLimit2DoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 106, "clk2", 100));
}

TEST(FullskewTimingCheckWindow, ZeroLimitsSimultaneousDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(0, 0));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 100));
}

TEST(FullskewTimingCheckWindow, ZeroLimitsAnyOrderedGapViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(0, 0));
  EXPECT_TRUE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 101));
  EXPECT_TRUE(mgr.CheckFullskewViolation("clk1", 101, "clk2", 100));
}

TEST(FullskewTimingCheckWindow, MismatchedDataSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 100, "other", 200));
}

TEST(FullskewTimingCheckWindow, MismatchedReferenceSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("other", 100, "clk2", 200));
}

TEST(FullskewTimingCheckWindow, OtherKindsAreIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry timeskew;
  timeskew.kind = TimingCheckKind::kTimeskew;
  timeskew.ref_signal = "clk1";
  timeskew.data_signal = "clk2";
  timeskew.limit = 1;
  mgr.AddTimingCheck(timeskew);
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 200));
}

TEST(FullskewModeOracle, TimerModeTimecheckAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 105,
                                        true,
                                        5,
                                        false));
}

TEST(FullskewModeOracle, TimerModeTimecheckBeyondLimitViolates) {
  EXPECT_TRUE(ReportsFullskewViolation(100, 106,
                                       true,
                                       5,
                                       false));
}

TEST(FullskewModeOracle, TimerModeNewTimestampBeyondLimitViolates) {
  EXPECT_TRUE(ReportsFullskewViolation(100, 106,
                                       false,
                                       5,
                                       false));
}

TEST(FullskewModeOracle, TimerModeNewTimestampAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 105,
                                        false,
                                        5,
                                        false));
}

TEST(FullskewModeOracle, TimerModeSimultaneousDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 100,
                                        true,
                                        0,
                                        false));
}

TEST(FullskewModeOracle, EventModeTimecheckBeyondLimitViolates) {
  EXPECT_TRUE(ReportsFullskewViolation(100, 106,
                                       true,
                                       5,
                                       true));
}

TEST(FullskewModeOracle, EventModeTimecheckAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 105,
                                        true,
                                        5,
                                        true));
}

TEST(FullskewModeOracle, EventModeNewTimestampBeyondLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 200,
                                        false,
                                        5,
                                        true));
}

TEST(FullskewModeOracle, OutOfOrderEventDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 90, true,
                                        5,
                                        false));
  EXPECT_FALSE(ReportsFullskewViolation(100, 90, true,
                                        5,
                                        true));
}

// A timestamp whose condition holds opens a fresh window, regardless of the
// remain_active_flag; this also re-arms a dormant check.
TEST(FullskewRemainActiveFlag, HoldingConditionReplacesWindow) {
  EXPECT_EQ(FullskewSecondTimestampAction(true, false),
            FullskewWindowAction::kReplaceWindow);
  EXPECT_EQ(FullskewSecondTimestampAction(true, true),
            FullskewWindowAction::kReplaceWindow);
}

// A false-condition timestamp with remain_active_flag set leaves the open window
// in place and is otherwise discarded.
TEST(FullskewRemainActiveFlag, FalseConditionWithFlagIgnoresEvent) {
  EXPECT_EQ(FullskewSecondTimestampAction(false, true),
            FullskewWindowAction::kIgnore);
}

// A false-condition timestamp without remain_active_flag turns the check dormant.
TEST(FullskewRemainActiveFlag, FalseConditionWithoutFlagGoesDormant) {
  EXPECT_EQ(FullskewSecondTimestampAction(false, false),
            FullskewWindowAction::kGoDormant);
}

}
