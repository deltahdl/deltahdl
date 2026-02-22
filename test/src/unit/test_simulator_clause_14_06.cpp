// §14.6: Signals in multiple clocking blocks

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
// 15. Multiple clocking blocks
// =============================================================================
TEST(ClockingSim, MultipleClockingBlocks) {
  ClockingManager cmgr;

  ClockingBlock block1;
  block1.name = "cb_fast";
  block1.clock_signal = "clk_fast";
  block1.clock_edge = Edge::kPosedge;
  block1.default_input_skew = SimTime{1};
  block1.default_output_skew = SimTime{1};
  cmgr.Register(block1);

  ClockingBlock block2;
  block2.name = "cb_slow";
  block2.clock_signal = "clk_slow";
  block2.clock_edge = Edge::kNegedge;
  block2.default_input_skew = SimTime{5};
  block2.default_output_skew = SimTime{5};
  cmgr.Register(block2);

  EXPECT_EQ(cmgr.Count(), 2u);
  EXPECT_NE(cmgr.Find("cb_fast"), nullptr);
  EXPECT_NE(cmgr.Find("cb_slow"), nullptr);
  EXPECT_EQ(cmgr.Find("cb_fast")->clock_edge, Edge::kPosedge);
  EXPECT_EQ(cmgr.Find("cb_slow")->clock_edge, Edge::kNegedge);
}

} // namespace
