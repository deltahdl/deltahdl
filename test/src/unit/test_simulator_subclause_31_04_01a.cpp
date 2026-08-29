#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TimingCheckEntry MakeSkew(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSkew;
  tc.ref_signal = "clk1";
  tc.data_signal = "clk2";
  tc.limit = limit;
  return tc;
}

TEST(SkewTimingCheckWindow, DataStrictlyBeyondLimitViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk1", 100, "clk2", 106));
}

TEST(SkewTimingCheckWindow, DataAtLimitDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "clk2", 105));
}

TEST(SkewTimingCheckWindow, DataBeforeReferenceDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "clk2", 90));
}

TEST(SkewTimingCheckWindow, ZeroLimitSimultaneousDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(0));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "clk2", 100));
}

// §31.4.1: simultaneous transitions on the reference and data signals never
// report a violation -- the LRM calls this out for a zero limit, but it holds
// for any limit. Same instant, positive limit: no violation.
TEST(SkewTimingCheckWindow,
     SimultaneousTransitionDoesNotViolateAtPositiveLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "clk2", 100));
}

TEST(SkewTimingCheckWindow, ZeroLimitAnyLaterDataViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(0));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk1", 100, "clk2", 101));
}

TEST(SkewTimingCheckWindow, MismatchedDataSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("clk1", 100, "other", 200));
}

TEST(SkewTimingCheckWindow, MismatchedReferenceSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_FALSE(mgr.CheckSkewViolation("other", 100, "clk2", 200));
}

// §31.4.1: after a reference event, $skew shall never stop checking data
// events -- every data event occurring beyond the limit reports a violation,
// not just the first. Two successive data events past the same reference each
// violate.
TEST(SkewTimingCheckWindow, EveryLaterDataEventBeyondLimitViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk1", 100, "clk2", 106));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk1", 100, "clk2", 120));
}

// §31.4.1 claim 9 -- the check is event-based and evaluated only on a data
// event. A data event is the sole trigger for a verdict (ReferenceEvent yields
// none), and one occurring before any reference has been seen cannot violate;
// only after a reference arms the check does a data event report.
TEST(SkewStatefulCheck, DataEventIsTheTriggerAndNeedsAPriorReference) {
  SkewChecker chk(5);
  EXPECT_FALSE(chk.DataEvent(106));  // no reference yet: not armed, no verdict
  chk.ReferenceEvent(100);           // arm the check (produces no verdict)
  EXPECT_TRUE(chk.DataEvent(106));   // now the data event triggers the report
}

// §31.4.1 claim 10 -- the wait for a data event is open-ended: a data event
// arriving far later than the reference is still checked and reported.
TEST(SkewStatefulCheck, WaitsIndefinitelyForLateDataEvent) {
  SkewChecker chk(5);
  chk.ReferenceEvent(100);
  EXPECT_TRUE(chk.DataEvent(10000));  // arbitrarily late, still beyond limit
}

// §31.4.1 claim 10 -- a data event within the limit after the reference does
// not violate, even when it arrives late in absolute terms.
TEST(SkewStatefulCheck, DataEventWithinLimitDoesNotViolate) {
  SkewChecker chk(5);
  chk.ReferenceEvent(100);
  EXPECT_FALSE(chk.DataEvent(103));
}

// §31.4.1 claim 10 -- a second reference event before any data event cancels
// the first wait and starts a new one: the data event is measured from the
// later reference, so what would violate against the first reference does not
// violate against the second.
TEST(SkewStatefulCheck, SecondReferenceCancelsEarlierWait) {
  SkewChecker chk(5);
  chk.ReferenceEvent(100);  // first wait
  chk.ReferenceEvent(120);  // supersedes it
  // 124 is 24 past the first reference (would violate) but only 4 past the
  // second (within limit) -- measured from the second reference: no violation.
  EXPECT_FALSE(chk.DataEvent(124));
  // 130 is 10 past the second reference: violates.
  EXPECT_TRUE(chk.DataEvent(130));
}

// §31.4.1 claim 11 -- after a reference, checking never stops: every later
// data event beyond the limit reports a violation.
TEST(SkewStatefulCheck, EveryDataEventBeyondLimitReportsAfterReference) {
  SkewChecker chk(5);
  chk.ReferenceEvent(100);
  EXPECT_TRUE(chk.DataEvent(106));
  EXPECT_TRUE(chk.DataEvent(200));
  EXPECT_TRUE(chk.DataEvent(300));
}

// §31.4.1 claim 8 -- simultaneous reference and data transitions never violate,
// modeled statefully (data event at the reference instant).
TEST(SkewStatefulCheck, SimultaneousReferenceAndDataDoesNotViolate) {
  SkewChecker chk(0);
  chk.ReferenceEvent(100);
  EXPECT_FALSE(chk.DataEvent(100));
}

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
