#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §31.4.3 Syntax 31-11 / Table 31-9: the runtime timing-check store must
// round-trip the direction-dependent pair of limits alongside the
// edge-qualified reference and data signals.
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

// End-to-end: a $fullskew specify item with all seven positional slots
// — two edge-qualified events, both limits, notifier, event_based_flag,
// and remain_active_flag — lowers and runs.
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

// §31.4.3: when the reference event transitions first it is the
// timestamp event and the active window uses limit 1. With limit1=4 and
// ref_time=100, a data event at 105 is 5 units later — strictly greater
// than limit 1 — and violates.
TEST(FullskewTimingCheckWindow, DataBeyondLimit1Violates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_TRUE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 105));
}

// §31.4.3: $fullskew shall not report a violation if a new timestamp
// event occurs exactly at the expiration of the time limit — the
// inequality is strict, so a data event exactly `limit1` units after the
// reference does not violate.
TEST(FullskewTimingCheckWindow, DataAtLimit1DoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 104));
}

// §31.4.3: a data event well within limit 1 does not violate.
TEST(FullskewTimingCheckWindow, DataWithinLimit1DoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 102));
}

// §31.4.3: when the data event transitions first it is the timestamp
// event and limit 2 bounds the wait for the reference event. With
// limit2=6 and data_time=100, a reference at 107 is 7 units later —
// strictly greater than limit 2 — and violates.
TEST(FullskewTimingCheckWindow, ReferenceBeyondLimit2Violates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_TRUE(mgr.CheckFullskewViolation("clk1", 107, "clk2", 100));
}

// §31.4.3: a reference event exactly `limit2` units after the data event
// does not violate (strict inequality on the reverse-direction window).
TEST(FullskewTimingCheckWindow, ReferenceAtLimit2DoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 106, "clk2", 100));
}

// §31.4.3: a reference event within limit 2 of a preceding data event
// does not violate.
TEST(FullskewTimingCheckWindow, ReferenceWithinLimit2DoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 103, "clk2", 100));
}

// §31.4.3: simultaneous transitions on the reference and data signals
// shall not cause $fullskew to report a timing violation, even when the
// skew limit value is zero.
TEST(FullskewTimingCheckWindow, ZeroLimitsSimultaneousDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(0, 0));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 100));
}

// §31.4.3: with zero limits, any strictly-later second event violates
// the strict-inequality predicate in the direction determined by which
// event transitioned first.
TEST(FullskewTimingCheckWindow, ZeroLimitsAnyOrderedGapViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(0, 0));
  EXPECT_TRUE(mgr.CheckFullskewViolation("clk1", 100, "clk2", 101));
  EXPECT_TRUE(mgr.CheckFullskewViolation("clk1", 101, "clk2", 100));
}

// §31.4.3: both endpoint signals must match for a stored $fullskew entry
// to attribute a violation. A data event on a different signal is not
// attributable to this entry.
TEST(FullskewTimingCheckWindow, MismatchedDataSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("clk1", 100, "other", 200));
}

// §31.4.3: both endpoint signals must match — a reference event on a
// different signal is not attributable to this $fullskew entry.
TEST(FullskewTimingCheckWindow, MismatchedReferenceSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeFullskew(4, 6));
  EXPECT_FALSE(mgr.CheckFullskewViolation("other", 100, "clk2", 200));
}

// CheckFullskewViolation must only inspect $fullskew entries; sibling
// kinds in the same SpecifyManager store must not trigger a $fullskew
// violation.
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

// §31.4.3 default timer-based behaviour: a timecheck event arriving
// within the window cancels the timer and does not violate.
TEST(FullskewModeOracle, TimerModeTimecheckWithinLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 103,
                                        /*is_timecheck=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/false));
}

// §31.4.3 default timer-based behaviour: a timecheck event arriving
// exactly at the elapsed-limit boundary does not violate.
TEST(FullskewModeOracle, TimerModeTimecheckAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 105,
                                        /*is_timecheck=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/false));
}

// §31.4.3 default timer-based behaviour: when a timecheck event arrives
// strictly past the limit the timer has already elapsed and a violation
// is reported.
TEST(FullskewModeOracle, TimerModeTimecheckBeyondLimitViolates) {
  EXPECT_TRUE(ReportsFullskewViolation(100, 106,
                                       /*is_timecheck=*/true,
                                       /*limit=*/5,
                                       /*event_based_flag=*/false));
}

// §31.4.3 default timer-based behaviour: a fresh timestamp event
// arriving after the timer would have elapsed witnesses a violation for
// the prior window.
TEST(FullskewModeOracle, TimerModeNewTimestampBeyondLimitViolates) {
  EXPECT_TRUE(ReportsFullskewViolation(100, 106,
                                       /*is_timecheck=*/false,
                                       /*limit=*/5,
                                       /*event_based_flag=*/false));
}

// §31.4.3 explicit exact-expiration rule: a new timestamp event landing
// exactly at the elapsed-limit boundary shall not report a violation.
TEST(FullskewModeOracle, TimerModeNewTimestampAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 105,
                                        /*is_timecheck=*/false,
                                        /*limit=*/5,
                                        /*event_based_flag=*/false));
}

// §31.4.3 zero-limit timer mode: simultaneous events do not violate even
// when the limit is zero.
TEST(FullskewModeOracle, TimerModeSimultaneousDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 100,
                                        /*is_timecheck=*/true,
                                        /*limit=*/0,
                                        /*event_based_flag=*/false));
}

// §31.4.3 event-based mode: behaves like $skew for the window — only
// timecheck events strictly past the limit violate.
TEST(FullskewModeOracle, EventModeTimecheckBeyondLimitViolates) {
  EXPECT_TRUE(ReportsFullskewViolation(100, 106,
                                       /*is_timecheck=*/true,
                                       /*limit=*/5,
                                       /*event_based_flag=*/true));
}

// §31.4.3 event-based mode: a timecheck event exactly at the boundary
// does not violate ($skew strict inequality).
TEST(FullskewModeOracle, EventModeTimecheckAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 105,
                                        /*is_timecheck=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/true));
}

// §31.4.3 event-based mode: a fresh timestamp event past the limit does
// not itself report a violation — event mode waits for a timecheck event
// before evaluating, matching $skew.
TEST(FullskewModeOracle, EventModeNewTimestampBeyondLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 200,
                                        /*is_timecheck=*/false,
                                        /*limit=*/5,
                                        /*event_based_flag=*/true));
}

// §31.4.3 event-based mode: a timecheck event within the window ends it
// without reporting a violation.
TEST(FullskewModeOracle, EventModeTimecheckWithinLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 103,
                                        /*is_timecheck=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/true));
}

// §31.4.3 event-based mode: simultaneous transitions cannot violate even
// at zero limit (matches $skew's zero-limit carve-out).
TEST(FullskewModeOracle, EventModeSimultaneousDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 100,
                                        /*is_timecheck=*/true,
                                        /*limit=*/0,
                                        /*event_based_flag=*/true));
}

// Out-of-order events (an "earlier" next-event timestamp) must not be
// classified as a violation in either mode; the helper bails on
// `next_event_time <= timestamp_time`.
TEST(FullskewModeOracle, OutOfOrderEventDoesNotViolate) {
  EXPECT_FALSE(ReportsFullskewViolation(100, 90, /*is_timecheck=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/false));
  EXPECT_FALSE(ReportsFullskewViolation(100, 90, /*is_timecheck=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/true));
}

}  // namespace
