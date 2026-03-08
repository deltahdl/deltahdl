#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(ClockingSim, InputSkewSamplesBeforeClockEdge) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{2};
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
  EXPECT_EQ(sampled, 0xABu);
}

TEST(ClockingSim, OutputSkewDrivesAfterClockEdge) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data_out = f.ctx.CreateVariable("data_out", 8);
  data_out->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr,
                     {"cb",
                      Edge::kPosedge,
                      {0},
                      SimTime{5},
                      "data_out",
                      ClockingDir::kOutput});

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "data_out", 0x55, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(data_out->value.ToUint64(), 0x55u);
}

TEST(ClockingSim, PerSignalInputSkewOverride) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{5};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "fast_in";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{1};
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "fast_in").ticks, 1u);
  EXPECT_EQ(cmgr.GetInputSkew("cb", "other").ticks, 5u);
}

TEST(ClockingSim, PerSignalOutputSkewOverride) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{10};

  ClockingSignal sig;
  sig.signal_name = "fast_out";
  sig.direction = ClockingDir::kOutput;
  sig.skew = SimTime{2};
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetOutputSkew("cb", "fast_out").ticks, 2u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "other").ticks, 10u);
}

TEST(Clocking, PerSignalSkewOverridesDefault) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{5};
  block.default_output_skew = SimTime{10};

  ClockingSignal sig;
  sig.signal_name = "data_in";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{7};
  block.signals.push_back(sig);

  mgr.Register(block);

  auto skew = mgr.GetInputSkew("cb", "data_in");
  EXPECT_EQ(skew.ticks, 7u);

  auto default_skew = mgr.GetInputSkew("cb", "other_signal");
  EXPECT_EQ(default_skew.ticks, 5u);
}

}
