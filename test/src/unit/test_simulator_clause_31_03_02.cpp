#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

// §31.3.2 ($hold) defines the violation window relative to the reference
// (timestamp) event: begin = timestamp time, end = timestamp time + limit, with
// a violation when begin <= timecheck time < end -- the begin endpoint is part
// of the violation region and the end endpoint is not. CheckHoldViolation
// carries this; the reference signal is the timestamp event, so its time is the
// window origin.

TimingCheckEntry MakeHold(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = limit;
  return tc;
}

TEST(HoldTimingCheckWindow, TimecheckStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 103));
}

TEST(HoldTimingCheckWindow, BeginEndpointIncluded) {
  // begin = timestamp time; the begin endpoint is inside the violation region.
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 100));
}

TEST(HoldTimingCheckWindow, EndEndpointExcluded) {
  // end = timestamp time + limit; the end endpoint is outside the region.
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 105));
}

TEST(HoldTimingCheckWindow, WindowScalesWithLimit) {
  // The window [begin, begin+limit) tracks the limit: below begin and at the
  // end endpoint do not violate; the begin endpoint and interior do.
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(3));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 99));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 100));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 101));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 102));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 103));
}

TEST(HoldTimingCheckWindow, ZeroLimitNeverViolates) {
  // When the limit is zero the $hold check shall never issue a violation.
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(0));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 101));
}

}
