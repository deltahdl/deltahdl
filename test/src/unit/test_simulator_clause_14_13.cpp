// §14.13: Input sampling

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- clocking_direction: input sampling on posedge ---
TEST(SimA611, InputSamplingPosedge) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr, "cb", Edge::kPosedge, {0}, {0}, "data_in",
                     ClockingDir::kInput);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data_in"), 0xABu);
}

// --- negedge clocking block ---
TEST(SimA611, NegedgeClockEvent) {
  SimFixture f;
  ClockingManager cmgr;
  TestNegedgeSampling(f, cmgr);
}

// --- sampled value updates across edges ---
TEST(SimA611, SampledValueUpdatesAcrossEdges) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr, "cb", Edge::kPosedge, {0}, {0}, "data",
                     ClockingDir::kInput);

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

// Helper fixture for clocking simulation tests.
// Schedule posedge at a given time through the scheduler.
// Schedule negedge at a given time through the scheduler.
// =============================================================================
// 5. Clocking block input sampling (S14.6)
// =============================================================================
TEST(ClockingSim, InputSampling) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* sig_a = f.ctx.CreateVariable("sig_a", 16);
  sig_a->value = MakeLogic4VecVal(f.arena, 16, 0x1234);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "sig_a";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "sig_a"), 0x1234u);
}

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

TEST(Clocking, AttachSamplesOnClockEdge) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data_in = f.ctx.CreateVariable("data_in", 8);
  data_in->value = MakeLogic4VecVal(f.arena, 8, 0xAA);

  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "data_in";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  mgr.Register(block);

  mgr.Attach(f.ctx, f.scheduler);

  // Schedule clock posedge at t=10.
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&clk, &f]() {
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);

  f.scheduler.Run();

  // data_in should have been sampled.
  auto sampled = mgr.GetSampledValue("cb", "data_in");
  EXPECT_EQ(sampled, 0xAAu);
}

}  // namespace
