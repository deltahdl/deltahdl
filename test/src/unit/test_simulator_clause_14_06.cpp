#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SignalMultiBlockSim, TwoBlocksRegistered) {
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

TEST(SignalMultiBlockSim, SameSignalInTwoBlocksSampled) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAA);

  ClockingManager cmgr;

  ClockingBlock block1;
  block1.name = "cb1";
  block1.clock_signal = "clk";
  block1.clock_edge = Edge::kPosedge;
  block1.default_input_skew = SimTime{0};
  block1.default_output_skew = SimTime{0};
  ClockingSignal sig1;
  sig1.signal_name = "data";
  sig1.direction = ClockingDir::kInput;
  block1.signals.push_back(sig1);
  cmgr.Register(block1);

  ClockingBlock block2;
  block2.name = "cb2";
  block2.clock_signal = "clk";
  block2.clock_edge = Edge::kPosedge;
  block2.default_input_skew = SimTime{0};
  block2.default_output_skew = SimTime{0};
  ClockingSignal sig2;
  sig2.signal_name = "data";
  sig2.direction = ClockingDir::kInput;
  block2.signals.push_back(sig2);
  cmgr.Register(block2);

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  // Both blocks sample the same signal at the same clock edge.
  EXPECT_EQ(cmgr.GetSampledValue("cb1", "data"), 0xAAu);
  EXPECT_EQ(cmgr.GetSampledValue("cb2", "data"), 0xAAu);
}

TEST(SignalMultiBlockSim, SharedClockBothBlocksTriggered) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* sig_a = f.ctx.CreateVariable("sig_a", 8);
  sig_a->value = MakeLogic4VecVal(f.arena, 8, 0x11);
  auto* sig_b = f.ctx.CreateVariable("sig_b", 8);
  sig_b->value = MakeLogic4VecVal(f.arena, 8, 0x22);

  ClockingManager cmgr;

  ClockingBlock block1;
  block1.name = "cb1";
  block1.clock_signal = "clk";
  block1.clock_edge = Edge::kPosedge;
  block1.default_input_skew = SimTime{0};
  block1.default_output_skew = SimTime{0};
  ClockingSignal s1;
  s1.signal_name = "sig_a";
  s1.direction = ClockingDir::kInput;
  block1.signals.push_back(s1);
  cmgr.Register(block1);

  ClockingBlock block2;
  block2.name = "cb2";
  block2.clock_signal = "clk";
  block2.clock_edge = Edge::kPosedge;
  block2.default_input_skew = SimTime{0};
  block2.default_output_skew = SimTime{0};
  ClockingSignal s2;
  s2.signal_name = "sig_b";
  s2.direction = ClockingDir::kInput;
  block2.signals.push_back(s2);
  cmgr.Register(block2);

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  // Both blocks triggered by the same clock event.
  EXPECT_EQ(cmgr.GetSampledValue("cb1", "sig_a"), 0x11u);
  EXPECT_EQ(cmgr.GetSampledValue("cb2", "sig_b"), 0x22u);
}

}  // namespace
