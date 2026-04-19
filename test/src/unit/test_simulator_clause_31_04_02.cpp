#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §31.4.2 Syntax 31-10 / Table 31-8: the runtime timing-check store must
// round-trip the four positional fields of $timeskew — kind, the
// edge-qualified reference and data signals, and the timing_check_limit.
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

// §31.4.2 Syntax 31-10: a timing_check_event's event control is optional, so
// a $timeskew entry may carry SpecifyEdge::kNone on either side. The zero
// limit is the explicit boundary case for simultaneous transitions.
TEST(SystemTimingCheckSim, TimeskewEntryWithoutEdgesStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kTimeskew;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kNone;
  tc.data_signal = "d";
  tc.data_edge = SpecifyEdge::kNone;
  tc.limit = 0;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(stored.ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(stored.data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(stored.limit, 0u);
}

// End-to-end: a $timeskew specify item with all six positional slots
// (notifier, event_based_flag, remain_active_flag) lowers and runs.
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

// §31.4.2: a violation is reported only when the data event follows the
// reference event by strictly more than `limit`. With limit=5 and
// ref_time=100, a data event at 106 is 6 units later — strictly greater
// than the limit — and violates.
TEST(TimeskewTimingCheckWindow, DataStrictlyBeyondLimitViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_TRUE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 106));
}

// §31.4.2: $timeskew shall not report a violation if a new timestamp event
// occurs exactly at the expiration of the time limit — the inequality is
// strict, so a data event exactly `limit` units after the reference event
// does not violate.
TEST(TimeskewTimingCheckWindow, DataAtLimitDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 105));
}

// §31.4.2: a data event well within the allowed window does not violate.
TEST(TimeskewTimingCheckWindow, DataWithinLimitDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 103));
}

// §31.4.2's violation predicate is one-sided in the (timecheck - timestamp)
// direction; a data event preceding the reference event is not a $timeskew
// violation.
TEST(TimeskewTimingCheckWindow, DataBeforeReferenceDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 90));
}

// §31.4.2: simultaneous transitions on the reference and data signals shall
// not cause $timeskew to report a violation, even when the skew limit is
// zero.
TEST(TimeskewTimingCheckWindow, ZeroLimitSimultaneousDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(0));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 100));
}

// §31.4.2: with a zero limit, any strictly-later data event violates the
// strict-inequality predicate.
TEST(TimeskewTimingCheckWindow, ZeroLimitAnyLaterDataViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(0));
  EXPECT_TRUE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 101));
}

// §31.4.2's violation must match both endpoint signals; a data event on a
// different signal is not attributable to this $timeskew entry.
TEST(TimeskewTimingCheckWindow, MismatchedDataSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "other", 200));
}

// §31.4.2's violation must match both endpoint signals; a reference event
// on a different signal is not attributable to this $timeskew entry.
TEST(TimeskewTimingCheckWindow, MismatchedReferenceSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("other", 100, "clk2", 200));
}

// CheckTimeskewViolation must only inspect $timeskew entries; sibling
// kinds in the same SpecifyManager store must not trigger a $timeskew
// violation.
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

// §31.4.2 default timer-based behaviour: a data event arriving within the
// limit window cancels the timer and does not violate.
TEST(TimeskewModeOracle, TimerModeDataWithinLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 103, /*is_data=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/false));
}

// §31.4.2 default timer-based behaviour: a data event arriving exactly at
// the elapsed-limit boundary does not violate (strict inequality).
TEST(TimeskewModeOracle, TimerModeDataAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 105, /*is_data=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/false));
}

// §31.4.2 default timer-based behaviour: when a data event arrives strictly
// past the limit the timer has already elapsed and a violation is reported.
TEST(TimeskewModeOracle, TimerModeDataBeyondLimitViolates) {
  EXPECT_TRUE(ReportsTimeskewViolation(100, 106, /*is_data=*/true,
                                       /*limit=*/5,
                                       /*event_based_flag=*/false));
}

// §31.4.2 default timer-based behaviour: a fresh reference event arriving
// inside the window silently re-arms the timer with no violation.
TEST(TimeskewModeOracle, TimerModeNewReferenceWithinLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 104, /*is_data=*/false,
                                        /*limit=*/5,
                                        /*event_based_flag=*/false));
}

// §31.4.2 explicit exact-expiration rule: a new timestamp event landing
// exactly at the elapsed limit boundary shall not report a violation.
TEST(TimeskewModeOracle, TimerModeNewReferenceAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 105, /*is_data=*/false,
                                        /*limit=*/5,
                                        /*event_based_flag=*/false));
}

// §31.4.2 default timer-based behaviour: a fresh reference event arriving
// after the timer would have elapsed witnesses a violation for the prior
// interval.
TEST(TimeskewModeOracle, TimerModeNewReferenceBeyondLimitViolates) {
  EXPECT_TRUE(ReportsTimeskewViolation(100, 106, /*is_data=*/false,
                                       /*limit=*/5,
                                       /*event_based_flag=*/false));
}

// §31.4.2 zero-limit timer mode: simultaneous events do not violate even
// when the limit is zero.
TEST(TimeskewModeOracle, TimerModeSimultaneousDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 100, /*is_data=*/true,
                                        /*limit=*/0,
                                        /*event_based_flag=*/false));
}

// §31.4.2 event-based mode (event_based_flag set, remain_active_flag set):
// behaves like $skew — only data events strictly past the limit violate.
TEST(TimeskewModeOracle, EventModeDataBeyondLimitViolates) {
  EXPECT_TRUE(ReportsTimeskewViolation(100, 106, /*is_data=*/true,
                                       /*limit=*/5,
                                       /*event_based_flag=*/true));
}

// §31.4.2 event-based mode: a data event at exactly the limit boundary
// does not violate ($skew strict inequality).
TEST(TimeskewModeOracle, EventModeDataAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 105, /*is_data=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/true));
}

// §31.4.2 event-based mode: a fresh reference event past the limit does
// not itself report a violation — event mode waits for a data event,
// matching $skew's behaviour.
TEST(TimeskewModeOracle, EventModeNewReferenceBeyondLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 200, /*is_data=*/false,
                                        /*limit=*/5,
                                        /*event_based_flag=*/true));
}

// §31.4.2 event-based mode: data within the window does not violate.
TEST(TimeskewModeOracle, EventModeDataWithinLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 103, /*is_data=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/true));
}

// §31.4.2 event-based mode: simultaneous transitions cannot violate even
// at zero limit (matches $skew's zero-limit carve-out).
TEST(TimeskewModeOracle, EventModeSimultaneousDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 100, /*is_data=*/true,
                                        /*limit=*/0,
                                        /*event_based_flag=*/true));
}

// Out-of-order events (an "earlier" next-event timestamp) must not be
// classified as a violation in either mode; the helper bails on
// `next_event_time <= ref_time`.
TEST(TimeskewModeOracle, OutOfOrderEventDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 90, /*is_data=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/false));
  EXPECT_FALSE(ReportsTimeskewViolation(100, 90, /*is_data=*/true,
                                        /*limit=*/5,
                                        /*event_based_flag=*/true));
}

}  // namespace
