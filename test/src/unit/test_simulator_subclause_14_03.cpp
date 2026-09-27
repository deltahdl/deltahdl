#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"

using namespace delta;

namespace {

TEST(ClockingBlockSim, RegisterBlock) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  const auto* found = cmgr.Find("cb");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->clock_signal, "clk");
  EXPECT_EQ(found->clock_edge, Edge::kPosedge);
}

TEST(ClockingBlockSim, DefaultSkewApplied) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{3};
  block.default_output_skew = SimTime{5};

  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "data").ticks, 3u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "other").ticks, 5u);
}

TEST(ClockingBlockSim, InoutSignalSkew) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{2};
  block.default_output_skew = SimTime{4};

  ClockingSignal sig;
  sig.signal_name = "bidir";
  sig.direction = ClockingDir::kInout;
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "bidir").ticks, 2u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "bidir").ticks, 4u);
}

TEST(ClockingBlockSim, MultipleBlocks) {
  ClockingManager cmgr;

  ClockingBlock b1;
  b1.name = "cb_fast";
  b1.clock_signal = "fast_clk";
  b1.clock_edge = Edge::kPosedge;
  b1.default_input_skew = SimTime{1};
  b1.default_output_skew = SimTime{1};
  cmgr.Register(b1);

  ClockingBlock b2;
  b2.name = "cb_slow";
  b2.clock_signal = "slow_clk";
  b2.clock_edge = Edge::kNegedge;
  b2.default_input_skew = SimTime{5};
  b2.default_output_skew = SimTime{5};
  cmgr.Register(b2);

  EXPECT_EQ(cmgr.Count(), 2u);
  EXPECT_NE(cmgr.Find("cb_fast"), nullptr);
  EXPECT_NE(cmgr.Find("cb_slow"), nullptr);
}

TEST(ClockingBlockSim, NegedgeClockEvent) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  TestNegedgeSampling(f, cmgr);
}

TEST(ClockingBlockSim, SimContextClockingManagerAccess) {
  ClockingSimFixture f;
  ClockingManager cmgr;

  ClockingBlock block;
  block.name = "main_cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  f.ctx.SetClockingManager(&cmgr);
  EXPECT_EQ(f.ctx.GetClockingManager(), &cmgr);
}

TEST(ClockingBlockSim, RegisterAndFind) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb_main";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{2};
  block.default_output_skew = SimTime{3};

  mgr.Register(block);
  EXPECT_EQ(mgr.Count(), 1u);

  const auto* found = mgr.Find("cb_main");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->clock_signal, "clk");
  EXPECT_EQ(found->default_input_skew.ticks, 2u);
}

TEST(ClockingBlockSim, FindNonexistent) {
  ClockingManager mgr;
  EXPECT_EQ(mgr.Find("nonexistent"), nullptr);
}

TEST(ClockingBlockSim, DefaultSkewAppliedToAllSignals) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{3};
  block.default_output_skew = SimTime{7};

  ClockingSignal in_sig;
  in_sig.signal_name = "a";
  in_sig.direction = ClockingDir::kInput;
  block.signals.push_back(in_sig);

  ClockingSignal out_sig;
  out_sig.signal_name = "b";
  out_sig.direction = ClockingDir::kOutput;
  block.signals.push_back(out_sig);

  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "a").ticks, 3u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "b").ticks, 7u);
}

TEST(ClockingBlockSim, DefaultInputSkew) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{5};
  block.default_output_skew = SimTime{10};
  mgr.Register(block);

  auto skew = mgr.GetInputSkew("cb", "data_in");
  EXPECT_EQ(skew.ticks, 5u);
}

TEST(ClockingBlockSim, OutputSkew) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{1};
  block.default_output_skew = SimTime{3};
  mgr.Register(block);

  auto skew = mgr.GetOutputSkew("cb", "data_out");
  EXPECT_EQ(skew.ticks, 3u);
}

TEST(ClockingBlockSim, EdgeClockEdgeRegistered) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kEdge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  const auto* found = cmgr.Find("cb");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->clock_edge, Edge::kEdge);
}

// §14.3 (printed page 354) with §23.6: a clocking event may name its clock by a
// hierarchical name, `@(posedge top.clk)`, and the block then fires at that
// signal's edges as at a local one's. Dropped, the program's `@(cb)` waited for
// ever on a free-running clock.
TEST(ClockingBlockSim, HierarchicallyNamedClockFiresFromAProgram) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  logic clk = 0; logic [3:0] d;\n"
                 "  always #5 clk = ~clk;\n"
                 "  p pi(d);\n"
                 "endmodule\n"
                 "program p(output logic [3:0] d);\n"
                 "  clocking cb @(posedge top.clk); output d; endclocking\n"
                 "  initial begin @(cb); cb.d <= 4'd5; @(cb); $display(\"prog "
                 "at %0t\", $time); end\n"
                 "endprogram\n",
                 f),
      "prog at 15\n");
}

// The same clocking event in a submodule's block.
TEST(ClockingBlockSim, HierarchicallyNamedClockFiresFromASubmodule) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  logic clk = 0; logic [3:0] d;\n"
                 "  always #5 clk = ~clk;\n"
                 "  sub si(d);\n"
                 "endmodule\n"
                 "module sub(output logic [3:0] d);\n"
                 "  clocking cb @(posedge top.clk); output d; endclocking\n"
                 "  initial begin @(cb); cb.d <= 4'd5; @(cb); $display(\"sub "
                 "at %0t\", $time); $finish; end\n"
                 "endmodule\n",
                 f),
      "sub at 15\n$finish at time 15\n");
}

// §14.9 (printed page 359) with §25.5: a program's block clocked by a signal of
// its interface port, `@(posedge a.clk)` with `bus_A.test a`, fires at that
// edge, samples `data = a.data` and drives `write = a.write` through the port.
TEST(ClockingBlockSim, ClockReachedThroughAnInterfacePortFires) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface bus_A(input clk);\n"
                 "  logic [15:0] data;\n"
                 "  logic write;\n"
                 "  modport test(input data, output write, input clk);\n"
                 "endinterface\n"
                 "program test(bus_A.test a);\n"
                 "  clocking cd1 @(posedge a.clk);\n"
                 "    input data = a.data;\n"
                 "    output write = a.write;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    @(cd1);\n"
                 "    $display(\"t=%0t data=%0d\", $time, cd1.data);\n"
                 "    cd1.write <= 1;\n"
                 "    #1 $display(\"t=%0t write=%0d\", $time, a.write);\n"
                 "    $finish;\n"
                 "  end\n"
                 "endprogram\n"
                 "module top;\n"
                 "  logic clk = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  bus_A a(clk);\n"
                 "  initial begin a.data = 33; a.write = 0; #60 $finish; end\n"
                 "  test main(a);\n"
                 "endmodule\n",
                 f),
      "t=5 data=33\nt=6 write=1\n$finish at time 6\n");
}

}  // namespace
