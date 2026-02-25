// §14.13: Input sampling

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

// --- clocking_direction: input sampling on posedge ---
TEST(SimA611, InputSamplingPosedge) {
  SimA611Fixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

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

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data_in"), 0xABu);
}

// --- negedge clocking block ---
TEST(SimA611, NegedgeClockEvent) {
  SimA611Fixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* data = f.ctx.CreateVariable("neg_data", 8);
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

// --- sampled value updates across edges ---
TEST(SimA611, SampledValueUpdatesAcrossEdges) {
  SimA611Fixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  // First posedge at t=10 samples 0x11
  SchedulePosedge(f, clk, 10);

  // Change data at t=12
  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  };
  f.scheduler.ScheduleEvent(SimTime{12}, Region::kActive, ev_data);

  // Negedge at t=15
  ScheduleNegedge(f, clk, 15);

  // Second posedge at t=20 samples 0x22
  SchedulePosedge(f, clk, 20);

  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x22u);
}

}  // namespace
