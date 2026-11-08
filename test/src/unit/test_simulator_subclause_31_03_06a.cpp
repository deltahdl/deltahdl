#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

TimingCheckEntry MakeRecrem(uint64_t recovery_limit, uint64_t removal_limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "rst";
  tc.limit = recovery_limit;
  tc.limit2 = removal_limit;
  return tc;
}

TEST(RecremTimingCheckWindow, DataFirstStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 97));
}

TEST(RecremTimingCheckWindow, DataFirstBeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 96));
}

TEST(RecremTimingCheckWindow, DataFirstEndEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
}

TEST(RecremTimingCheckWindow, DataSecondStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 105));
}

TEST(RecremTimingCheckWindow, DataSecondEndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 108));
}

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

TEST(RecremTimingCheckWindow, BothLimitsZeroNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(0, 0));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 99));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 101));
}

}  // namespace
