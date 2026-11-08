#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

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
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 100));
}

TEST(HoldTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 105));
}

TEST(HoldTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(3));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 99));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 100));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 101));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 102));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 103));
}

TEST(HoldTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(0));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 101));
}

}  // namespace
