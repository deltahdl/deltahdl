// §14.5: Hierarchical expressions

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/clocking.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string_view>

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
// 12. Hierarchical access to clocking signals (S14.10)
// =============================================================================
TEST(ClockingSim, HierarchicalAccess) {
  ClockingSimFixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto *data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xCC);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "data_in";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  auto sampled = cmgr.GetSampledValue("cb", "data_in");
  EXPECT_EQ(sampled, 0xCCu);
}

} // namespace
