// §14.4: Input and output skews

#include <gtest/gtest.h>

#include <cstdint>

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

struct SimA611Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

void SchedulePosedge(SimA611Fixture& f, Variable* clk, uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

void ScheduleNegedge(SimA611Fixture& f, Variable* clk, uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

namespace {

// --- clocking_skew: per-signal skew overrides default ---
TEST(SimA611, PerSignalSkewOverride) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{10};
  block.default_output_skew = SimTime{10};

  ClockingSignal sig;
  sig.signal_name = "fast_in";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{2};
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "fast_in").ticks, 2u);
  EXPECT_EQ(cmgr.GetInputSkew("cb", "other").ticks, 10u);
}

}  // namespace
