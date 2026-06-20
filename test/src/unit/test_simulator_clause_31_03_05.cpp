#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

// §31.3.5 ($recovery) defines the violation window relative to the reference
// (timestamp) event: begin = timestamp time, end = timestamp time + limit, with
// a violation when begin <= timecheck time < end -- only the end of the window
// is excluded from the violation region. CheckRecoveryViolation carries this;
// the window is byte-identical to $hold (§31.3.2). A zero limit collapses the
// window so no transition can violate it.

TimingCheckEntry MakeRecovery(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecovery;
  tc.ref_signal = "rst";
  tc.data_signal = "clk";
  tc.limit = limit;
  return tc;
}

TEST(RecoveryTimingCheckWindow, TimecheckStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 103));
}

TEST(RecoveryTimingCheckWindow, BeginEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 100));
}

TEST(RecoveryTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 105));
}

TEST(RecoveryTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(3));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 99));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 100));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 101));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 102));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 103));
}

TEST(RecoveryTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(0));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 100));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 99));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 101));
}

}  // namespace
