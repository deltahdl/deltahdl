// Non-LRM tests

#include <cstdint>
#include <string_view>
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// 19. Sampled value persists across multiple edges
// =============================================================================
TEST(ClockingSim, SampledValueUpdatesOnEachEdge) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr, "cb", Edge::kPosedge, {0}, {0}, "data",
                     ClockingDir::kInput);

  // First posedge: data = 0x11
  auto* ev1 = f.scheduler.GetEventPool().Acquire();
  ev1->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev1);

  // Change data value between posedges.
  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  };
  f.scheduler.ScheduleEvent(SimTime{12}, Region::kActive, ev_data);

  // Negedge.
  auto* ev_neg = f.scheduler.GetEventPool().Acquire();
  ev_neg->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev_neg);

  // Second posedge: data = 0x22
  auto* ev2 = f.scheduler.GetEventPool().Acquire();
  ev2->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{20}, Region::kActive, ev2);

  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x22u);
}

}  // namespace
