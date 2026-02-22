// §14.11: Cycle delay: ##

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/clocking.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

// Helper fixture for clocking simulation tests.
struct ClockingSimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, /*seed=*/42};
};

// Schedule posedge at a given time through the scheduler.
void SchedulePosedge(ClockingSimFixture &f, Variable *clk, uint64_t time) {
  auto *ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

// Schedule negedge at a given time through the scheduler.
void ScheduleNegedge(ClockingSimFixture &f, Variable *clk, uint64_t time) {
  auto *ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

namespace {

// =============================================================================
// 7. Cycle delay ##N (S14.11)
// =============================================================================
TEST(ClockingSim, CycleDelayWaitsNEdges) {
  ClockingSimFixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  cmgr.SetDefaultClocking("cb");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "cb");

  f.ctx.SetClockingManager(&cmgr);

  auto *counter = f.ctx.CreateVariable("counter", 32);
  counter->value = MakeLogic4VecVal(f.arena, 32, 0);

  SchedulePosedge(f, clk, 10);
  ScheduleNegedge(f, clk, 15);
  SchedulePosedge(f, clk, 20);
  ScheduleNegedge(f, clk, 25);
  SchedulePosedge(f, clk, 30);

  uint32_t edge_count = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler,
                            [&edge_count]() { edge_count++; });

  cmgr.Attach(f.ctx, f.scheduler);
  f.scheduler.Run();
  EXPECT_GE(edge_count, 3u);
}

}  // namespace
