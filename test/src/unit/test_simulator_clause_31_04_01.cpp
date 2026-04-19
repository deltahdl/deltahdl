#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §31.4.1 Syntax 31-9 / Table 31-7: the runtime timing-check store must
// round-trip all four positional fields of $skew — kind, the edge-qualified
// reference and data signals, and the timing_check_limit.
TEST(SystemTimingCheckSim, SkewEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSkew;
  tc.ref_signal = "clk1";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "clk2";
  tc.data_edge = SpecifyEdge::kNegedge;
  tc.limit = 3;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kSkew);
  EXPECT_EQ(stored.ref_signal, "clk1");
  EXPECT_EQ(stored.data_signal, "clk2");
  EXPECT_EQ(stored.limit, 3u);
}

// §31.4.1 Syntax 31-9: a timing_check_event's event control is optional,
// so a $skew entry may carry SpecifyEdge::kNone on one or both sides. The
// zero limit is also §31.4.1's explicit boundary case for simultaneous
// transitions.
TEST(SystemTimingCheckSim, SkewEntryWithoutEdgesStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSkew;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kNone;
  tc.data_signal = "d";
  tc.data_edge = SpecifyEdge::kNone;
  tc.limit = 0;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kSkew);
  EXPECT_EQ(stored.ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(stored.data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(stored.limit, 0u);
}

// Register a `$skew` timing check with ref = clk1 (timestamp event),
// data = clk2 (timecheck event), and the given limit.
TimingCheckEntry MakeSkew(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSkew;
  tc.ref_signal = "clk1";
  tc.data_signal = "clk2";
  tc.limit = limit;
  return tc;
}

// §31.4.1: a violation is reported when the data event follows the
// reference event by strictly more than `limit`. With limit=5 and
// ref_time=100, a data event at 106 is 6 units later — strictly greater
// than the limit — and violates.
TEST(SkewTimingCheckWindow, DataStrictlyBeyondLimitViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk1", 100, "clk2", 106));
}

// §31.4.1: the limit itself is the maximum allowed skew; a data event
// exactly `limit` units after the reference event does not violate.
TEST(SkewTimingCheckWindow, DataAtLimitDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "clk2", 105));
}

// §31.4.1: a data event within the allowed skew window does not violate.
TEST(SkewTimingCheckWindow, DataWithinLimitDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "clk2", 103));
}

// §31.4.1: $skew is a one-sided check — a data event preceding the
// reference event is not a $skew violation.
TEST(SkewTimingCheckWindow, DataBeforeReferenceDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "clk2", 90));
}

// §31.4.1: the zero-limit carve-out — simultaneous transitions do not
// violate when the skew limit is zero.
TEST(SkewTimingCheckWindow, ZeroLimitSimultaneousDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(0));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "clk2", 100));
}

// §31.4.1: with a zero limit, any strictly-later data event violates.
TEST(SkewTimingCheckWindow, ZeroLimitAnyLaterDataViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(0));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk1", 100, "clk2", 101));
}

// §31.4.1: the check must match both endpoint signals. A data event on a
// different signal is not attributable to this $skew entry.
TEST(SkewTimingCheckWindow, MismatchedDataSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "other", 200));
}

// §31.4.1: the check must match both endpoint signals. A reference event
// on a different signal is not attributable to this $skew entry.
TEST(SkewTimingCheckWindow, MismatchedReferenceSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("other", 100, "clk2", 200));
}

// CheckSkewViolation must only inspect $skew entries; unrelated kinds in
// the same SpecifyManager store must not trigger a $skew violation.
TEST(SkewTimingCheckWindow, OtherKindsAreIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry setup;
  setup.kind = TimingCheckKind::kSetup;
  setup.ref_signal = "clk1";
  setup.data_signal = "clk2";
  setup.limit = 1;
  mgr.AddTimingCheck(setup);
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "clk2", 200));
}

}  // namespace
