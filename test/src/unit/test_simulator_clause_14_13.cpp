#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(InputSamplingSim, PosedgeSamplesCurrentValue) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data_in", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data_in"), 0xABu);
}

TEST(InputSamplingSim, NegedgeSamplesCurrentValue) {
  SimFixture f;
  ClockingManager cmgr;
  TestNegedgeSampling(f, cmgr);
}

TEST(InputSamplingSim, SampledValueUpdatesAcrossEdges) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);

  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  };
  f.scheduler.ScheduleEvent(SimTime{12}, Region::kActive, ev_data);

  ScheduleNegedge(f, clk, 15);

  SchedulePosedge(f, clk, 20);

  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x22u);
}

TEST(InputSamplingSim, AttachSamplesOnClockEdge) {
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

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&clk, &f]() {
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);

  f.scheduler.Run();

  auto sampled = mgr.GetSampledValue("cb", "data_in");
  EXPECT_EQ(sampled, 0xAAu);
}

TEST(InputSamplingSim, ZeroSkewInputSamplesInObservedRegion) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x10);

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
  sig.skew = SimTime{0};
  sig.is_explicit_zero_skew = true;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  // Schedule Active: clock posedge + data update in same time step.
  auto* ev_clk = f.scheduler.GetEventPool().Acquire();
  ev_clk->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev_clk);

  // Active-region data change at same time — #0 skew input should see this.
  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x20);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev_data);

  f.scheduler.Run();

  // #0 skew: samples in Observed, so sees Active-region update.
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x20u);
}

TEST(InputSamplingSim, SameSignalInMultipleBlocks) {
  ClockingSimFixture f;
  auto* clk1 = f.ctx.CreateVariable("clk1", 1);
  clk1->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* clk2 = f.ctx.CreateVariable("clk2", 1);
  clk2->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;

  // Block 1: posedge clk1
  ClockingBlock block1;
  block1.name = "cb1";
  block1.clock_signal = "clk1";
  block1.clock_edge = Edge::kPosedge;
  block1.default_input_skew = SimTime{0};
  block1.default_output_skew = SimTime{0};
  ClockingSignal sig1;
  sig1.signal_name = "data";
  sig1.direction = ClockingDir::kInput;
  block1.signals.push_back(sig1);
  cmgr.Register(block1);

  // Block 2: posedge clk2
  ClockingBlock block2;
  block2.name = "cb2";
  block2.clock_signal = "clk2";
  block2.clock_edge = Edge::kPosedge;
  block2.default_input_skew = SimTime{0};
  block2.default_output_skew = SimTime{0};
  ClockingSignal sig2;
  sig2.signal_name = "data";
  sig2.direction = ClockingDir::kInput;
  block2.signals.push_back(sig2);
  cmgr.Register(block2);

  cmgr.Attach(f.ctx, f.scheduler);

  // Posedge clk1 at t=10, data=0x11
  SchedulePosedge(f, clk1, 10);

  // Change data at t=15
  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev_data);

  // Posedge clk2 at t=20, data=0x22
  SchedulePosedge(f, clk2, 20);

  f.scheduler.Run();

  // Each block samples independently at its own clocking event.
  EXPECT_EQ(cmgr.GetSampledValue("cb1", "data"), 0x11u);
  EXPECT_EQ(cmgr.GetSampledValue("cb2", "data"), 0x22u);
}

TEST(InputSamplingSim, InoutSignalSampledAsInput) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x55);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInout});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x55u);
}

TEST(InputSamplingSim, SampledBeforeBlockEventFires) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x42);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  // Register an edge callback that reads the sampled value.
  uint64_t value_seen_in_callback = 0;
  cmgr.RegisterEdgeCallback(
      "cb", f.ctx, f.scheduler,
      [&cmgr, &value_seen_in_callback]() {
        value_seen_in_callback = cmgr.GetSampledValue("cb", "data");
      });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  // Edge callback fires after sampling, so it sees the sampled value.
  EXPECT_EQ(value_seen_in_callback, 0x42u);
}

}  // namespace
