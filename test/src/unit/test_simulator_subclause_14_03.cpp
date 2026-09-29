#include <gtest/gtest.h>

#include <string>

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
      RunCapture("module sub(output logic [3:0] d);\n"
                 "  clocking cb @(posedge top.clk); output d; endclocking\n"
                 "  initial begin @(cb); cb.d <= 4'd5; @(cb); $display(\"sub "
                 "at %0t\", $time); $finish; end\n"
                 "endmodule\n"
                 "module top;\n"
                 "  logic clk = 0; logic [3:0] d;\n"
                 "  always #5 clk = ~clk;\n"
                 "  sub si(d);\n"
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

// §14.3 with §9.4.2.3: the clocking event may carry an `iff` qualifier, and
// the block samples and its event fires only at the edges where it holds.
TEST(ClockingBlockSim, ClockingEventIffQualifierGatesTheEdges) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0, en = 0;\n"
                       "  logic [7:0] d = 1;\n"
                       "  clocking cb @(posedge clk iff en);\n"
                       "    input d;\n"
                       "  endclocking\n"
                       "  always #5 clk = ~clk;\n"
                       "  initial begin\n"
                       "    #7 d = 2;\n"
                       "    #10 d = 3;\n"
                       "    #4 en = 1;\n"
                       "  end\n"
                       "  initial begin\n"
                       "    @(cb);\n"
                       "    $display(\"t=%0t cb.d=%0d\", $time, cb.d);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=25 cb.d=3\n"
            "$finish at time 25\n");
}

// §14.3 with §23.9: the `iff` condition of a block declared in a module
// instance names that instance's variables.
TEST(ClockingBlockSim, ClockingEventIffReadsTheBlocksInstance) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m(input logic clk);\n"
                 "  logic en = 0;\n"
                 "  int n;\n"
                 "  clocking cb @(posedge clk iff en);\n"
                 "  endclocking\n"
                 "  always @(cb) n++;\n"
                 "  initial #12 en = 1;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  logic clk = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  m u(clk);\n"
                 "  initial #40 begin $display(\"n=%0d\", u.n); $finish; end\n"
                 "endmodule\n",
                 f),
      "n=3\n"
      "$finish at time 40\n");
}

// §14.3 with §23.6 (printed pages 354 and 741): a clocking block is a named
// item of the module declaring it, so the parent reaches its submodule's block
// by hierarchical name -- `@(u.cb)` waits for its event, `u.cb.d` reads its
// sample and `u.cb.q <= 77` drives through it. The elaborator reported `u.cb`
// as undeclared in module m.
TEST(ClockingBlockSim, SubmoduleClockingBlockByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(input logic clk);\n"
                       "  logic [7:0] d = 3, q = 0;\n"
                       "  clocking cb @(posedge clk);\n"
                       "    input d;\n"
                       "    output q;\n"
                       "  endclocking\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  m u(clk);\n"
                       "  initial begin\n"
                       "    @(u.cb);\n"
                       "    $write(\"%0t:%0d \", $time, u.cb.d);\n"
                       "    u.cb.q <= 77;\n"
                       "    #1 $display(\"%0t:%0d\", $time, u.q);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5:3 6:77\n$finish at time 6\n");
}

// §14.3 with §27.5 and §23.6: a clocking block written in a named generate
// block is a named item of the block's scope, so a process outside the block
// reaches it as `g.cb` -- `@(g.cb)` waits for its event, `g.cb.d` reads its
// sample and `g.cb.q <= 77` drives through it. None answered to the path, and
// the wait never woke.
TEST(ClockingBlockSim, GenerateBlockClockingBlockByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  logic [7:0] d = 4, q = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  if (1) begin : g\n"
                       "    clocking cb @(posedge clk);\n"
                       "      input d;\n"
                       "      output q;\n"
                       "    endclocking\n"
                       "  end\n"
                       "  initial begin\n"
                       "    @(g.cb);\n"
                       "    $write(\"%0t:%0d \", $time, g.cb.d);\n"
                       "    g.cb.q <= 77;\n"
                       "    #1 $display(\"%0t:%0d\", $time, q);\n"
                       "    $finish;\n"
                       "  end\n"
                       "  initial #60 $finish;\n"
                       "endmodule\n",
                       f),
            "5:4 6:77\n$finish at time 6\n");
}

// §14.3 with §23.6: the path to a generate block's clocking block may start at
// a submodule instance, `u.g.cb`, whose block samples that instance's signal.
TEST(ClockingBlockSim, SubmoduleGenerateBlockClockingBlockByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(input logic clk);\n"
                       "  logic [7:0] d = 6;\n"
                       "  if (1) begin : g\n"
                       "    clocking cb @(posedge clk);\n"
                       "      input d;\n"
                       "    endclocking\n"
                       "  end\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  m u(clk);\n"
                       "  initial begin\n"
                       "    @(u.g.cb);\n"
                       "    $display(\"%0t:%0d\", $time, u.g.cb.d);\n"
                       "    $finish;\n"
                       "  end\n"
                       "  initial #60 $finish;\n"
                       "endmodule\n",
                       f),
            "5:6\n$finish at time 5\n");
}

// §14.3 with §23.9 and §27.4: a clocking block names its signals and its clock
// as a reference written where it stands does, so in a generate block a bare
// name is that block's own declaration. `cb.e` sampled 0, `e` naming nothing
// outside the block, and a clock the block declared never fired.
TEST(ClockingBlockSim, GenerateBlockClockingBlockSamplesTheBlocksSignals) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  if (1) begin : g\n"
                       "    logic gclk = 0;\n"
                       "    logic [7:0] e = 8'd20;\n"
                       "    always #5 gclk = ~gclk;\n"
                       "    clocking cb @(posedge gclk);\n"
                       "      input e;\n"
                       "    endclocking\n"
                       "    initial begin\n"
                       "      @(cb);\n"
                       "      $display(\"%0t:%0d\", $time, cb.e);\n"
                       "      $finish;\n"
                       "    end\n"
                       "  end\n"
                       "  initial #60 $finish;\n"
                       "endmodule\n",
                       f),
            "5:20\n$finish at time 5\n");
}

// §14.3 with §27.4: each instance of a loop generate block is a scope of its
// own, so each declares its own clocking block, sampling its own signal and
// reached from outside by its index, `g[1].cb`. Every instance registered its
// block under the one name `cb`, and all of them reached the last.
TEST(ClockingBlockSim, LoopGenerateInstancesDeclareTheirOwnClockingBlocks) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "    logic [7:0] e;\n"
                       "    initial e = 8'(i + 20);\n"
                       "    clocking cb @(posedge clk);\n"
                       "      input e;\n"
                       "    endclocking\n"
                       "    initial begin\n"
                       "      @(cb);\n"
                       "      #(i) $write(\"in%0d:%0d \", i, cb.e);\n"
                       "    end\n"
                       "  end\n"
                       "  initial begin\n"
                       "    @(g[0].cb);\n"
                       "    #2 $display(\"out:%0d\", g[0].cb.e);\n"
                       "    $finish;\n"
                       "  end\n"
                       "  initial #60 $finish;\n"
                       "endmodule\n",
                       f),
            "in0:20 in1:21 out:20\n$finish at time 7\n");
}

}  // namespace
