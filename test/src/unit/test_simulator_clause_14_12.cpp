// §14.12: Default clocking

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"
#include "helpers_clocking.h"

using namespace delta;

// Helper fixture for clocking simulation tests.
// Schedule posedge at a given time through the scheduler.

// Schedule negedge at a given time through the scheduler.

namespace {

// =============================================================================
// 8. Default clocking block (S14.12)
// =============================================================================
TEST(ClockingSim, DefaultClockingBlock) {
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
}

// --- clocking_declaration: default clocking ---
TEST(SimA611, DefaultClocking) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "sys_cb";
  block.clock_signal = "sys_clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{1};
  block.default_output_skew = SimTime{2};
  cmgr.Register(block);

  cmgr.SetDefaultClocking("sys_cb");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "sys_cb");
}

}  // namespace
