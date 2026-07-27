#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SystemTimingCheckSim, TimeskewEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kTimeskew;
  tc.ref_signal = "clk1";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "clk2";
  tc.data_edge = SpecifyEdge::kPosedge;
  tc.limit = 5;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(stored.ref_signal, "clk1");
  EXPECT_EQ(stored.data_signal, "clk2");
  EXPECT_EQ(stored.limit, 5u);
}

TEST(TimingCheckCommandSim, TimeskewWithFlagsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
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

TimingCheckEntry MakeTimeskew(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kTimeskew;
  tc.ref_signal = "clk1";
  tc.data_signal = "clk2";
  tc.limit = limit;
  return tc;
}

TEST(TimeskewTimingCheckWindow, DataStrictlyBeyondLimitViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_TRUE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 106));
}

TEST(TimeskewTimingCheckWindow, DataAtLimitDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 105));
}

TEST(TimeskewTimingCheckWindow, ZeroLimitSimultaneousDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(0));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 100));
}

TEST(TimeskewTimingCheckWindow, ZeroLimitAnyLaterDataViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(0));
  EXPECT_TRUE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 101));
}

TEST(TimeskewTimingCheckWindow, MismatchedDataSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "other", 200));
}

TEST(TimeskewTimingCheckWindow, MismatchedReferenceSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("other", 100, "clk2", 200));
}

TEST(TimeskewTimingCheckWindow, OtherKindsAreIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry skew;
  skew.kind = TimingCheckKind::kSkew;
  skew.ref_signal = "clk1";
  skew.data_signal = "clk2";
  skew.limit = 1;
  mgr.AddTimingCheck(skew);
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 200));
}

TEST(TimeskewModeOracle, TimerModeDataWithinLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 103, true, 5, false));
}

TEST(TimeskewModeOracle, TimerModeDataAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 105, true, 5, false));
}

TEST(TimeskewModeOracle, TimerModeDataBeyondLimitViolates) {
  EXPECT_TRUE(ReportsTimeskewViolation(100, 106, true, 5, false));
}

TEST(TimeskewModeOracle, TimerModeNewReferenceAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 105, false, 5, false));
}

TEST(TimeskewModeOracle, TimerModeNewReferenceBeyondLimitViolates) {
  EXPECT_TRUE(ReportsTimeskewViolation(100, 106, false, 5, false));
}

TEST(TimeskewModeOracle, TimerModeSimultaneousDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 100, true, 0, false));
}

TEST(TimeskewModeOracle, EventModeDataBeyondLimitViolates) {
  EXPECT_TRUE(ReportsTimeskewViolation(100, 106, true, 5, true));
}

TEST(TimeskewModeOracle, EventModeDataAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 105, true, 5, true));
}

TEST(TimeskewModeOracle, EventModeNewReferenceBeyondLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 200, false, 5, true));
}

TEST(TimeskewModeOracle, OutOfOrderEventDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 90, true, 5, false));
  EXPECT_FALSE(ReportsTimeskewViolation(100, 90, true, 5, true));
}

// --- Stateful dormancy behavior (§31.4.2) -------------------------------
// The following observe the timer-based/event-based dormancy rules that the
// per-event oracle above cannot express, through the TimeskewChecker model.

// Timer-based default: with no data event, the violation fires when the limit
// elapses after the reference.
TEST(TimeskewStatefulCheck, TimerModeTimeoutReportsWhenLimitElapses) {
  TimeskewChecker chk(/*limit=*/5, /*event_based_flag=*/false,
                      /*remain_active_flag=*/false);
  chk.ReferenceEvent(100);
  EXPECT_TRUE(chk.Timeout());
}

// After a timer-based violation the check is dormant and reports nothing more
// until the next reference; a fresh reference re-arms it.
TEST(TimeskewStatefulCheck, TimerModeDormantUntilNextReference) {
  TimeskewChecker chk(5, false, false);
  chk.ReferenceEvent(100);
  EXPECT_TRUE(chk.Timeout());
  EXPECT_FALSE(chk.Timeout());       // dormant: no further violations
  EXPECT_FALSE(chk.DataEvent(200));  // still dormant even for a late data event
  chk.ReferenceEvent(300);           // next reference re-arms
  EXPECT_TRUE(chk.Timeout());
}

// Timer-based: a data event within the limit reports nothing and turns the
// check dormant immediately, so the pending timeout never fires.
TEST(TimeskewStatefulCheck, TimerModeDataWithinLimitCancelsAndGoesDormant) {
  TimeskewChecker chk(5, false, false);
  chk.ReferenceEvent(100);
  EXPECT_FALSE(chk.DataEvent(103));  // within the limit: no violation
  EXPECT_FALSE(chk.Timeout());       // dormant: the timeout is cancelled
}

// Event-based with both flags set behaves like $skew: every data event beyond
// the limit reports a violation and the check stays armed.
TEST(TimeskewStatefulCheck, EventModeBothFlagsBehavesLikeSkew) {
  TimeskewChecker chk(5, /*event_based_flag=*/true,
                      /*remain_active_flag=*/true);
  chk.ReferenceEvent(100);
  EXPECT_TRUE(chk.DataEvent(106));
  EXPECT_TRUE(chk.DataEvent(200));  // still armed, reports again
  EXPECT_TRUE(chk.DataEvent(300));
  EXPECT_FALSE(chk.Timeout());  // event-based: the timer never fires
}

// Event-based with only the event_based_flag set is $skew-like but turns
// dormant after reporting its first violation.
TEST(TimeskewStatefulCheck, EventModeOnlyFlagDormantAfterFirstViolation) {
  TimeskewChecker chk(5, true, /*remain_active_flag=*/false);
  chk.ReferenceEvent(100);
  EXPECT_TRUE(chk.DataEvent(106));   // first violation
  EXPECT_FALSE(chk.DataEvent(200));  // dormant afterward
}

// A data event within the limit is not a violation and, in event-based mode,
// does not make the check dormant -- a later beyond-limit data event still
// reports (matching $skew's continued checking).
TEST(TimeskewStatefulCheck, EventModeDataWithinLimitKeepsCheckArmed) {
  TimeskewChecker chk(5, true, true);
  chk.ReferenceEvent(100);
  EXPECT_FALSE(chk.DataEvent(103));  // within limit: no violation, stays armed
  EXPECT_TRUE(chk.DataEvent(110));
}

// A conditioned reference whose condition is false turns the check dormant when
// remain_active_flag is clear.
TEST(TimeskewStatefulCheck, FalseConditionedReferenceGoesDormantWhenFlagClear) {
  TimeskewChecker chk(5, false, /*remain_active_flag=*/false);
  chk.ReferenceEvent(100);
  chk.ReferenceEvent(150, /*condition_holds=*/false);  // dormant
  EXPECT_FALSE(chk.Timeout());
}

// With remain_active_flag set, the same false-conditioned reference is ignored
// and the window opened by the earlier reference still stands.
TEST(TimeskewStatefulCheck, FalseConditionedReferenceIgnoredWhenFlagSet) {
  TimeskewChecker chk(5, false, /*remain_active_flag=*/true);
  chk.ReferenceEvent(100);
  chk.ReferenceEvent(150, /*condition_holds=*/false);  // ignored
  EXPECT_TRUE(chk.Timeout());  // original window still armed
}

// A reference whose condition holds re-arms a dormant check.
TEST(TimeskewStatefulCheck, TrueConditionedReferenceReArmsDormantCheck) {
  TimeskewChecker chk(5, false, false);
  chk.ReferenceEvent(100);
  chk.ReferenceEvent(150, /*condition_holds=*/false);  // dormant
  EXPECT_FALSE(chk.Timeout());
  chk.ReferenceEvent(200, /*condition_holds=*/true);  // re-arms
  EXPECT_TRUE(chk.Timeout());
}

}  // namespace
