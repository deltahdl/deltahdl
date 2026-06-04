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

  EXPECT_EQ(cmgr.GetSampledValue("cb1", "sig_a"), 0x11u);
  EXPECT_EQ(cmgr.GetSampledValue("cb2", "sig_b"), 0x22u);
}

// §14.6: blocks sharing a clock share its synchronization event. The converse
// edge of that rule is that the shared event is keyed to the specific clock --
// a block driven by a different clock is not synchronized by it. Two blocks on
// clk_a and one on clk_b: pulsing only clk_a samples the clk_a blocks while the
// clk_b block stays unsampled, even though every block's watcher is attached.
TEST(SignalMultiBlockSim, DifferentClockBlockNotSynchronized) {
  ClockingSimFixture f;
  auto* clk_a = f.ctx.CreateVariable("clk_a", 1);
  clk_a->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* clk_b = f.ctx.CreateVariable("clk_b", 1);
  clk_b->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* sig_a = f.ctx.CreateVariable("sig_a", 8);
  sig_a->value = MakeLogic4VecVal(f.arena, 8, 0x11);
  auto* sig_b = f.ctx.CreateVariable("sig_b", 8);
  sig_b->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  auto* sig_c = f.ctx.CreateVariable("sig_c", 8);
  sig_c->value = MakeLogic4VecVal(f.arena, 8, 0x33);

  ClockingManager cmgr;

  ClockingBlock block1;
  block1.name = "cb1";
  block1.clock_signal = "clk_a";
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
  block2.clock_signal = "clk_a";
  block2.clock_edge = Edge::kPosedge;
  block2.default_input_skew = SimTime{0};
  block2.default_output_skew = SimTime{0};
  ClockingSignal s2;
  s2.signal_name = "sig_b";
  s2.direction = ClockingDir::kInput;
  block2.signals.push_back(s2);
  cmgr.Register(block2);

  ClockingBlock block3;
  block3.name = "cb3";
  block3.clock_signal = "clk_b";
  block3.clock_edge = Edge::kPosedge;
  block3.default_input_skew = SimTime{0};
  block3.default_output_skew = SimTime{0};
  ClockingSignal s3;
  s3.signal_name = "sig_c";
  s3.direction = ClockingDir::kInput;
  block3.signals.push_back(s3);
  cmgr.Register(block3);

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk_a, 10);
  f.scheduler.Run();

  // The two blocks sharing clk_a sample at its edge.
  EXPECT_EQ(cmgr.GetSampledValue("cb1", "sig_a"), 0x11u);
  EXPECT_EQ(cmgr.GetSampledValue("cb2", "sig_b"), 0x22u);
  // The clk_b block was not synchronized by the clk_a edge, so its signal
  // (nonzero, so 0 means unsampled) was never captured.
  EXPECT_EQ(cmgr.GetSampledValue("cb3", "sig_c"), 0u);
}

// §14.6 ties the shared synchronization event to the same clock, which the LRM
// parenthesizes as the clocking expression -- i.e. the clocking event, edge
// included, not merely the clock signal. Two blocks naming the same signal but
// opposite edges therefore do NOT share a synchronization event: a posedge
// fires only the posedge block. This pins that production keys the event on the
// edge (CheckClockEdge), so same-signal/different-edge is a different event.
TEST(SignalMultiBlockSim, SameClockSignalOppositeEdgesNotShared) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* sig_p = f.ctx.CreateVariable("sig_p", 8);
  sig_p->value = MakeLogic4VecVal(f.arena, 8, 0x44);
  auto* sig_n = f.ctx.CreateVariable("sig_n", 8);
  sig_n->value = MakeLogic4VecVal(f.arena, 8, 0x55);

  ClockingManager cmgr;

  ClockingBlock block_pos;
  block_pos.name = "cb_pos";
  block_pos.clock_signal = "clk";
  block_pos.clock_edge = Edge::kPosedge;
  block_pos.default_input_skew = SimTime{0};
  block_pos.default_output_skew = SimTime{0};
  ClockingSignal sp;
  sp.signal_name = "sig_p";
  sp.direction = ClockingDir::kInput;
  block_pos.signals.push_back(sp);
  cmgr.Register(block_pos);

  ClockingBlock block_neg;
  block_neg.name = "cb_neg";
  block_neg.clock_signal = "clk";
  block_neg.clock_edge = Edge::kNegedge;
  block_neg.default_input_skew = SimTime{0};
  block_neg.default_output_skew = SimTime{0};
  ClockingSignal sn;
  sn.signal_name = "sig_n";
  sn.direction = ClockingDir::kInput;
  block_neg.signals.push_back(sn);
  cmgr.Register(block_neg);

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  // The posedge block synchronizes on the rising edge and samples its signal.
  EXPECT_EQ(cmgr.GetSampledValue("cb_pos", "sig_p"), 0x44u);
  // The negedge block, though it names the same clock signal, is a distinct
  // clocking event and is not synchronized by the rising edge (nonzero signal,
  // so 0 means unsampled).
  EXPECT_EQ(cmgr.GetSampledValue("cb_neg", "sig_n"), 0u);
}

}
