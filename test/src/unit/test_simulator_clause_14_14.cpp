// §14.14: Global clocking


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
// 9. Global clocking (S14.13)
// =============================================================================
TEST(ClockingSim, GlobalClockingBlock) {
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

// --- clocking_declaration: global clocking ---
TEST(SimA611, GlobalClocking) {
  ClockingManager cmgr;
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
  EXPECT_TRUE(cmgr.Find("gclk")->is_global);
}

}  // namespace
