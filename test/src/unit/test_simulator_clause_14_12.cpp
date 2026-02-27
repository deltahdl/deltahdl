// §14.12: Default clocking


#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast.h"
#include "simulation/clocking.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

// Helper fixture for clocking simulation tests.
// Schedule posedge at a given time through the scheduler.
void SchedulePosedge(ClockingSimFixture& f, Variable* clk, uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

// Schedule negedge at a given time through the scheduler.
void ScheduleNegedge(ClockingSimFixture& f, Variable* clk, uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

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

void SchedulePosedge(SimFixture& f, Variable* clk, uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

void ScheduleNegedge(SimFixture& f, Variable* clk, uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
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
