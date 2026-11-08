#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

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

TEST(SkewTimingCheckWindow, EveryLaterDataEventBeyondLimitViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSkew(5));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk1", 100, "clk2", 106));
  EXPECT_TRUE(mgr.CheckSkewViolation("clk1", 100, "clk2", 120));
}

TEST(SkewStatefulCheck, DataEventIsTheTriggerAndNeedsAPriorReference) {
  SkewChecker chk(5);
  EXPECT_FALSE(chk.DataEvent(106));
  chk.ReferenceEvent(100);
  EXPECT_TRUE(chk.DataEvent(106));
}

TEST(SkewStatefulCheck, WaitsIndefinitelyForLateDataEvent) {
  SkewChecker chk(5);
  chk.ReferenceEvent(100);
  EXPECT_TRUE(chk.DataEvent(10000));
}

TEST(SkewStatefulCheck, DataEventWithinLimitDoesNotViolate) {
  SkewChecker chk(5);
  chk.ReferenceEvent(100);
  EXPECT_FALSE(chk.DataEvent(103));
}

TEST(SkewStatefulCheck, SecondReferenceCancelsEarlierWait) {
  SkewChecker chk(5);
  chk.ReferenceEvent(100);
  chk.ReferenceEvent(120);
  EXPECT_FALSE(chk.DataEvent(124));
  EXPECT_TRUE(chk.DataEvent(130));
}

TEST(SkewStatefulCheck, EveryDataEventBeyondLimitReportsAfterReference) {
  SkewChecker chk(5);
  chk.ReferenceEvent(100);
  EXPECT_TRUE(chk.DataEvent(106));
  EXPECT_TRUE(chk.DataEvent(200));
  EXPECT_TRUE(chk.DataEvent(300));
}

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
