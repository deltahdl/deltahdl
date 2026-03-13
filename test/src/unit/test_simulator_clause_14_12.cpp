#include <gtest/gtest.h>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/clocking.h"

using namespace delta;

namespace {

TEST(DefaultClockingSim, SetAndGetDefaultClocking) {
  ClockingManager cmgr;
  EXPECT_TRUE(cmgr.GetDefaultClocking().empty());

  ClockingBlock block;
  block.name = "sys_cb";
  block.clock_signal = "sys_clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{1};
  block.default_output_skew = SimTime{2};
  cmgr.Register(block);

  cmgr.SetDefaultClocking("sys_cb");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "sys_cb");

  const auto* found = cmgr.Find("sys_cb");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->default_input_skew.ticks, 1u);
  EXPECT_EQ(found->default_output_skew.ticks, 2u);
}

TEST(DefaultClockingSim, DefaultClockingPreservesSkews) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{3};
  block.default_output_skew = SimTime{5};
  cmgr.Register(block);

  cmgr.SetDefaultClocking("cb");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "cb");

  const auto* found = cmgr.Find("cb");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->default_input_skew.ticks, 3u);
  EXPECT_EQ(found->default_output_skew.ticks, 5u);
}

TEST(DefaultClockingSim, DefaultClockingInitiallyEmpty) {
  ClockingManager cmgr;
  EXPECT_TRUE(cmgr.GetDefaultClocking().empty());
}

}  // namespace
