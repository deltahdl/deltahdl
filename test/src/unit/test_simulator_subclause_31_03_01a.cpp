#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

TimingCheckEntry MakeSetup(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = limit;
  return tc;
}

TEST(SetupTimingCheckWindow, TimestampStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(10));
  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 95));
}

TEST(SetupTimingCheckWindow, BeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(10));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 90));
}

TEST(SetupTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(10));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 100));
}

TEST(SetupTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(3));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 96));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 97));
  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 98));
  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 100));
}

TEST(SetupTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetup(0));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 101));
}

}  // namespace
