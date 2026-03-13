#include <gtest/gtest.h>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/clocking.h"

using namespace delta;

namespace {

TEST(GlobalClockingSim, SetAndGetGlobalClocking) {
  ClockingManager cmgr;
  EXPECT_TRUE(cmgr.GetGlobalClocking().empty());

  ClockingBlock block;
  block.name = "gclk";
  block.clock_signal = "clk_global";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  block.is_global = true;
  cmgr.Register(block);

  cmgr.SetGlobalClocking("gclk");
  EXPECT_EQ(cmgr.GetGlobalClocking(), "gclk");

  const auto* found = cmgr.Find("gclk");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_global);
}

TEST(GlobalClockingSim, GlobalClockingInitiallyEmpty) {
  ClockingManager cmgr;
  EXPECT_TRUE(cmgr.GetGlobalClocking().empty());
}

TEST(GlobalClockingSim, GlobalAndDefaultCoexist) {
  ClockingManager cmgr;

  ClockingBlock gblock;
  gblock.name = "gclk";
  gblock.clock_signal = "sys_clk";
  gblock.clock_edge = Edge::kPosedge;
  gblock.is_global = true;
  cmgr.Register(gblock);
  cmgr.SetGlobalClocking("gclk");

  ClockingBlock dblock;
  dblock.name = "dclk";
  dblock.clock_signal = "bus_clk";
  dblock.clock_edge = Edge::kPosedge;
  cmgr.Register(dblock);
  cmgr.SetDefaultClocking("dclk");

  EXPECT_EQ(cmgr.GetGlobalClocking(), "gclk");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "dclk");
  EXPECT_NE(cmgr.Find("gclk"), nullptr);
  EXPECT_NE(cmgr.Find("dclk"), nullptr);
}

TEST(GlobalClockingSim, GlobalClockingIsGlobalFlag) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "gc";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.is_global = true;
  cmgr.Register(block);

  const auto* found = cmgr.Find("gc");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_global);
  EXPECT_EQ(found->clock_edge, Edge::kPosedge);
}

}  // namespace
