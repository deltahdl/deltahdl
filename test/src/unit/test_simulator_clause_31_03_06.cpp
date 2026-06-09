#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

// limit holds the recovery limit (governs the data-second window) and limit2
// the removal limit (governs the data-first window), matching the $recovery +
// $removal decomposition of $recrem.
TimingCheckEntry MakeRecrem(uint64_t recovery_limit, uint64_t removal_limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "rst";
  tc.limit = recovery_limit;
  tc.limit2 = removal_limit;
  return tc;
}

// Data event first: window is (timecheck - removal_limit, timecheck]; a data
// transition strictly inside violates.
TEST(RecremTimingCheckWindow, DataFirstStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 97));
}

// The beginning of the data-first window is excluded from the violation region.
TEST(RecremTimingCheckWindow, DataFirstBeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 96));
}

// The end of the data-first window is included, so a simultaneous reference and
// data event reports a violation.
TEST(RecremTimingCheckWindow, DataFirstEndEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
}

// Data event second: window is [timestamp, timestamp + recovery_limit); a data
// transition strictly inside violates.
TEST(RecremTimingCheckWindow, DataSecondStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 105));
}

// The end of the data-second window is excluded from the violation region.
TEST(RecremTimingCheckWindow, DataSecondEndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 108));
}

// Each limit independently scales the side of the window it governs: removal_limit
// the data-first side, recovery_limit the data-second side.
TEST(RecremTimingCheckWindow, WindowsScaleWithLimits) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(7, 3));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 96));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 97));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 98));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 106));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 107));
}

// When both limits are zero the check never reports a violation.
TEST(RecremTimingCheckWindow, BothLimitsZeroNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(0, 0));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 99));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 101));
}

}
