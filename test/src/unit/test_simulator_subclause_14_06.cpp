#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_stmt.h"
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

TEST(SignalMultiBlockSim, SharedNegedgeClockBothBlocksTriggered) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* sig_a = f.ctx.CreateVariable("sig_a", 8);
  sig_a->value = MakeLogic4VecVal(f.arena, 8, 0x11);
  auto* sig_b = f.ctx.CreateVariable("sig_b", 8);
  sig_b->value = MakeLogic4VecVal(f.arena, 8, 0x22);

  ClockingManager cmgr;

  ClockingBlock block1;
  block1.name = "cb1";
  block1.clock_signal = "clk";
  block1.clock_edge = Edge::kNegedge;
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
  block2.clock_edge = Edge::kNegedge;
  block2.default_input_skew = SimTime{0};
  block2.default_output_skew = SimTime{0};
  ClockingSignal s2;
  s2.signal_name = "sig_b";
  s2.direction = ClockingDir::kInput;
  block2.signals.push_back(s2);
  cmgr.Register(block2);

  cmgr.Attach(f.ctx, f.scheduler);

  ScheduleNegedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb1", "sig_a"), 0x11u);
  EXPECT_EQ(cmgr.GetSampledValue("cb2", "sig_b"), 0x22u);
}

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

  EXPECT_EQ(cmgr.GetSampledValue("cb1", "sig_a"), 0x11u);
  EXPECT_EQ(cmgr.GetSampledValue("cb2", "sig_b"), 0x22u);
  EXPECT_EQ(cmgr.GetSampledValue("cb3", "sig_c"), 0u);
}

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

  EXPECT_EQ(cmgr.GetSampledValue("cb_pos", "sig_p"), 0x44u);
  EXPECT_EQ(cmgr.GetSampledValue("cb_neg", "sig_n"), 0u);
}

TEST(SignalMultiBlockSim, BlocksOnOneClockShareItsEventsFromSource) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  logic clk = 0, k2 = 0, en = 0;\n"
          "  int d = 0, q = 0;\n"
          "  int n1 = 0, n2 = 0, n3 = 0, n4 = 0, n5 = 0, t1 = -1, t2 = -1, t3 "
          "= -1;\n"
          "  int s1, s2, s3;\n"
          "  always #5 clk = ~clk;\n"
          "  always #3 k2 = ~k2;\n"
          "  initial begin #8 d = 1; #10 en = 1; end\n"
          "  clocking cb1 @(posedge clk); input #2 d; endclocking\n"
          "  clocking cb2 @(posedge clk); input #2 d; output q; endclocking\n"
          "  clocking cb3 @(negedge clk); input d; inout q; endclocking\n"
          "  clocking cb4 @(posedge clk iff en); endclocking\n"
          "  clocking cb5 @(posedge clk iff en); endclocking\n"
          "  clocking cb6 @(posedge k2); input clk; endclocking\n"
          "  always @(cb1) begin n1++; t1 = $time; end\n"
          "  always @(cb2) begin n2++; t2 = $time; end\n"
          "  always @(cb3) begin n3++; t3 = $time; end\n"
          "  always @(cb4) n4++;\n"
          "  always @(cb5) n5++;\n"
          "  initial begin\n"
          "    @(cb2) cb2.q <= 4;\n"
          "    @(cb3) cb3.q <= 6;\n"
          "  end\n"
          "  initial #28 begin\n"
          "    $display(\"%0d %0d %0d %0d %0d\", n1, n2, n3, n4, n5);\n"
          "    $display(\"%0d %0d %0d\", t1, t2, t3);\n"
          "    $display(\"%0d %0d %0d q=%0d clk=%0d\", cb1.d, cb2.d, cb3.d, q, "
          "cb6.clk);\n"
          "    $finish;\n"
          "  end\n"
          "endmodule\n",
          f),
      "3 3 2 1 1\n25 25 20\n1 1 1 q=6 clk=1\n$finish at time 28\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
