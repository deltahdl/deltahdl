#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

// Register a `$setup` timing check with ref = clk (timecheck event),
// data = data (timestamp event), and the given limit.
TimingCheckEntry MakeSetup(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = limit;
  return tc;
}

// Window is (timecheck - limit, timecheck) = (90, 100). A timestamp strictly
// inside reports a violation.
TEST(SetupTimingCheckWindow, TimestampStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(10));
  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 95));
}

// §31.3.1: end points of the window are not part of the violation region.
// Begin endpoint = timecheck - limit.
TEST(SetupTimingCheckWindow, BeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(10));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 90));
}

// §31.3.1: end points of the window are not part of the violation region.
// End endpoint = timecheck time itself.
TEST(SetupTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(10));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 100));
}

// Timestamp strictly before the window (earlier than begin) is outside and
// does not violate.
TEST(SetupTimingCheckWindow, TimestampBeforeWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(10));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 85));
}

// Timestamp strictly after the timecheck is outside the window.
TEST(SetupTimingCheckWindow, TimestampAfterTimecheckDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(10));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 105));
}

// Re-run the interior and endpoint cases at a different limit to pin down
// that the window actually scales with `limit` rather than a constant.
// With limit=3 and timecheck=100, begin shifts to 97 and the interior holds
// exactly two integer points (98 and 99).
TEST(SetupTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(3));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 96));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 97));
  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 98));
  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 100));
}

// §31.3.1: when the limit is zero, `$setup` shall never issue a violation.
// Exercise the case that would otherwise be most suspect (equal times).
TEST(SetupTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(0));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 101));
}

}  // namespace
