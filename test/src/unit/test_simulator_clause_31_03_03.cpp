#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

TimingCheckEntry MakeSetuphold(uint64_t setup_limit, uint64_t hold_limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = setup_limit;
  tc.limit2 = hold_limit;
  return tc;
}

TEST(SetupholdTimingCheckWindow, DataFirstStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 94));
}

TEST(SetupholdTimingCheckWindow, DataFirstBeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 90));
}

TEST(SetupholdTimingCheckWindow, DataFirstEndEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
}

TEST(SetupholdTimingCheckWindow, DataSecondStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 103));
}

TEST(SetupholdTimingCheckWindow, DataSecondEndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(SetupholdTimingCheckWindow, WindowsScaleWithLimits) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(3, 7));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 96));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 97));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 98));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 106));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 107));
}

TEST(SetupholdTimingCheckWindow, BothLimitsZeroNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(0, 0));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 101));
}

}
