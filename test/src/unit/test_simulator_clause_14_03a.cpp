// §14.3: Clocking block declaration

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
// 1. Clocking block declaration with clock event (S14.3)
// =============================================================================
TEST(ClockingSim, DeclareWithClockEvent) {
  ClockingSimFixture f;
  ClockingManager cmgr;

  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  const auto *found = cmgr.Find("cb");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->clock_signal, "clk");
  EXPECT_EQ(found->clock_edge, Edge::kPosedge);
}

// =============================================================================
// 16. Negedge clock event
// =============================================================================
TEST(ClockingSim, NegedgeClockEvent) {
  ClockingSimFixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto *data = f.ctx.CreateVariable("neg_data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xDD);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb_neg";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kNegedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "neg_data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  ScheduleNegedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb_neg", "neg_data"), 0xDDu);
}

// =============================================================================
// 17. Inout direction signal
// =============================================================================
TEST(ClockingSim, InoutSignalDirection) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{2};
  block.default_output_skew = SimTime{3};

  ClockingSignal sig;
  sig.signal_name = "bidir";
  sig.direction = ClockingDir::kInout;
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "bidir").ticks, 2u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "bidir").ticks, 3u);
}

} // namespace
