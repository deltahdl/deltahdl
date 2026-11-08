#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

TimingCheckEntry MakeRemoval(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRemoval;
  tc.ref_signal = "rst";
  tc.data_signal = "clk";
  tc.limit = limit;
  return tc;
}

TEST(RemovalTimingCheckWindow, TimestampStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_TRUE(mgr.CheckRemovalViolation("rst", 100, "clk", 95));
}

TEST(RemovalTimingCheckWindow, BeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 90));
}

TEST(RemovalTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 100));
}

TEST(RemovalTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(3));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 96));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 97));
  EXPECT_TRUE(mgr.CheckRemovalViolation("rst", 100, "clk", 98));
  EXPECT_TRUE(mgr.CheckRemovalViolation("rst", 100, "clk", 99));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 100));
}

TEST(RemovalTimingCheckWindow, DataAfterReferenceNoViolation) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 105));
}

TEST(RemovalTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(0));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 100));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 99));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 101));
}

}  // namespace
