#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §24.3.2: procedural program code runs in the reactive region set, so a design
// variable written across a program connection is updated there. A program
// initial block that reads a design value and writes a design variable must do
// so while executing in the reactive region.
TEST(ProgramPortConnectionSim, ProgramDrivesDesignVariableInReactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial a <= 8'd42;\n"
      "  program p;\n"
      "    initial b = a;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 42u);
  EXPECT_EQ(b->value.ToUint64(), 42u);
}

// §24.3.2: a net reached through a program connection is driven and resolved in
// the reactive region set. A continuous assign inside a program drives a design
// net; the resolved net value must reflect that reactive-region drive.
TEST(ProgramPortConnectionSim, ProgramContinuousAssignDrivesDesignNet) {
  SimFixture f;
  auto* dnet = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] src;\n"
      "  wire  [7:0] dnet;\n"
      "  initial src <= 8'd55;\n"
      "  program p;\n"
      "    assign dnet = src;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "dnet");
  ASSERT_NE(dnet, nullptr);
  EXPECT_EQ(dnet->value.ToUint64(), 55u);
}

// §24.3.2: design processes that are sensitive to the variables and nets
// updated across the region boundary are woken in the active region set. A
// design always block sensitive to a variable written by a program must wake
// and observe the program's reactive-region update.
TEST(ProgramPortConnectionSim,
     DesignAlwaysSensitiveToProgramWriteObservesUpdate) {
  SimFixture f;
  auto* obs = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] crossed;\n"
      "  logic [7:0] observed;\n"
      "  initial observed = 8'd0;\n"
      "  always @(crossed) observed = crossed;\n"
      "  program p;\n"
      "    initial #1 crossed = 8'd77;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(obs, nullptr);
  EXPECT_EQ(obs->value.ToUint64(), 77u);
}

// §24.3.2: driving and resolution of a net happen right after an event changes
// a driver on a program net. A design process that samples the resolved net at
// a later time step must see the value produced by the program's
// reactive-region drive.
TEST(ProgramPortConnectionSim, NetResolutionImmediateOnProgramDriverChange) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module top;\n"
      "  logic [3:0] src;\n"
      "  wire  [3:0] resolved;\n"
      "  logic [3:0] sampled;\n"
      "  initial begin\n"
      "    sampled = 4'd0;\n"
      "    src = 4'd0;\n"
      "    #1 src = 4'd5;\n"
      "    #1 sampled = resolved;\n"
      "  end\n"
      "  program p;\n"
      "    assign resolved = src;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "sampled");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->value.ToUint64(), 5u);
}

// §24.3.2 (worked example): the program's continuous assign is held until the
// Reactive region, and the design always it triggers does not run until the
// Active region of the next pass, so the simulator must iterate the whole
// scheduling loop. The design always therefore still fires from the
// program-driven net change.
TEST(ProgramPortConnectionSim, MultiIterationLoopProgramAssignDesignAlways) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module m;\n"
      "  logic r;\n"
      "  wire  dw2;\n"
      "  logic [7:0] hits;\n"
      "  initial begin\n"
      "    hits = 8'd0;\n"
      "    r = 1'b0;\n"
      "    #10 r = 1'b1;\n"
      "  end\n"
      "  always @(dw2) hits = hits + 8'd1;\n"
      "  program p;\n"
      "    assign dw2 = r;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_GE(hits->value.ToUint64(), 1u);
}

// §24.3.2 (across an actual program port connection): a program instantiated
// with ports drives a design net through its output port. The drive and
// resolution happen in the reactive region set, and a design always block
// sensitive to that net is woken in the active region set, so it captures the
// program-driven value. This exercises the port-binding path (input/output
// bindings lowered as reactive continuous assigns), not a nested hierarchical
// reference.
TEST(ProgramPortConnectionSim,
     ProgramOutputPortDrivesDesignNetAndWakesDesignAlways) {
  SimFixture f;
  auto* cap = RunAndFindVar(
      "program p(input din, output dout);\n"
      "  assign dout = din;\n"
      "endprogram\n"
      "module top;\n"
      "  logic stim;\n"
      "  wire  pnet;\n"
      "  logic captured;\n"
      "  initial begin\n"
      "    captured = 1'b0;\n"
      "    stim = 1'b0;\n"
      "    #1 stim = 1'b1;\n"
      "  end\n"
      "  always @(pnet) captured = pnet;\n"
      "  p p_i(.din(stim), .dout(pnet));\n"
      "endmodule\n",
      f, "captured");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->value.ToUint64(), 1u);
}

// §24.3.2 (across an actual program port connection): a design variable on the
// other side of a program output port is updated in the reactive region set.
// The program reads a design value through its input port and drives a design
// variable through its output port; the final variable value reflects the
// reactive-region update carried across the port connection.
TEST(ProgramPortConnectionSim,
     ProgramOutputPortUpdatesDesignVariableInReactive) {
  SimFixture f;
  auto* cv = RunAndFindVar(
      "program p(input [7:0] din, output logic [7:0] dout);\n"
      "  assign dout = din;\n"
      "endprogram\n"
      "module top;\n"
      "  logic [7:0] feed;\n"
      "  logic [7:0] catch_var;\n"
      "  initial feed <= 8'd200;\n"
      "  p p_i(.din(feed), .dout(catch_var));\n"
      "endmodule\n",
      f, "catch_var");
  ASSERT_NE(cv, nullptr);
  EXPECT_EQ(cv->value.ToUint64(), 200u);
}

// §24.3.2 (worked example form, ordered port list): the LRM's own example wires
// the program with a positional port connection, `p p_i(dout, din)`, rather
// than by name. This drives the §23.3.2.1 ordered-connection path through the
// full pipeline. Data flows design net -> program input port -> the program's
// reactive continuous assign -> program output port -> design net, and the
// design `always` sensitive to that net fires. Because the program assign is
// held to the Reactive region and the design `always` runs in the Active region
// of a later scheduling pass, the counter only advances if the simulator
// iterates the whole loop and carries the reactive-region drive across the
// ordered port connection.
TEST(ProgramPortConnectionSim, PositionalPortConnectionCarriesReactiveDrive) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "program p(output pout, input pin);\n"
      "  assign pout = pin;\n"
      "endprogram\n"
      "module top;\n"
      "  logic r;\n"
      "  wire  din;\n"
      "  wire  dout;\n"
      "  logic [7:0] hits;\n"
      "  initial begin\n"
      "    hits = 8'd0;\n"
      "    r = 1'b0;\n"
      "    #5 r = 1'b1;\n"
      "  end\n"
      "  assign din = r;\n"
      "  p p_i(dout, din);\n"
      "  always @(dout) hits = hits + 8'd1;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_GE(hits->value.ToUint64(), 1u);
}

// §24.3.2 with §24.3: a program's blocking write to its output port as the
// last statement of its only initial reaches the connected design variable in
// that time step, before the implicit $finish ends the run.
TEST(ProgramPortConnectionSim, OutputPortWriteInTheLastStepReachesTheDesign) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "program p(output logic [7:0] q);\n"
      "  initial begin #4 q = 8'd77; end\n"
      "endprogram\n"
      "module top;\n"
      "  logic [7:0] q;\n"
      "  p pi(.q(q));\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->value.IsKnown());
  EXPECT_EQ(q->value.ToUint64(), 77u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 4u);
}

// §24.3.2 with §24.3.1: a program's input port net is driven by the design
// expression connected to it as soon as that changes, not in the Reactive
// region where the program's own code runs. A sequence the program declares,
// clocked by the port, is evaluated in the Observed region of the tick, so the
// program process waking on the same tick in the Reactive region sees it end
// at 15, 25 and 35.
TEST(ProgramPortConnectionSim,
     InputPortFollowsTheDesignBeforeTheObservedRegion) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program p(input logic clk);\n"
                 "  bit a = 1, b = 1;\n"
                 "  int n = 0;\n"
                 "  sequence e4;\n"
                 "    a ##1 b;\n"
                 "  endsequence\n"
                 "  initial forever @(posedge clk) if (e4.triggered) n++;\n"
                 "  initial #41 $display(\"n=%0d\", n);\n"
                 "endprogram\n"
                 "module t;\n"
                 "  bit clk;\n"
                 "  always #5 clk = ~clk;\n"
                 "  p u(clk);\n"
                 "  initial #45 $finish;\n"
                 "endmodule\n",
                 f),
      "n=3\n$finish at time 45\n");
}

// §24.3.2: a program's unpacked-array input port carries the design array
// connected to it, element by element, and its unpacked-array output port
// carries back what the program's code writes: the program reads d[1], 6,
// and writes 7 into o[0], which the design reads as os[0]. An input with a
// data type and no kind is a net (§23.2.2.3), and int is no type a net may
// have (§6.7.1), so the input is declared var.
TEST(ProgramPortConnectionSim, ArrayPortsCarryValuesBothWays) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program p(input logic clk, input var int d[2],\n"
                 "          output int o[2]);\n"
                 "  initial begin @(posedge clk) o[0] = d[1] + 1; #3; end\n"
                 "endprogram\n"
                 "module t;\n"
                 "  bit clk;\n"
                 "  int ds[2] = '{5, 6};\n"
                 "  int os[2];\n"
                 "  p u(clk, ds, os);\n"
                 "  initial #5 clk = 1;\n"
                 "  initial #6 $display(\"os=%0d\", os[0]);\n"
                 "endmodule\n",
                 f),
      "os=7\n");
}

// §24.3.2 with §24.3.1: an element of a program's unpacked-array input port
// follows the design array as a scalar input port does, so the sequence the
// program clocks by c[0] ends where the Reactive process reads it, at 15, 25
// and 35.
TEST(ProgramPortConnectionSim, ArrayInputPortFollowsTheDesignBeforeObserved) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program p(input logic c[2]);\n"
                 "  bit a = 1, b = 1;\n"
                 "  int n = 0;\n"
                 "  sequence e4;\n"
                 "    a ##1 b;\n"
                 "  endsequence\n"
                 "  initial forever @(posedge c[0]) if (e4.triggered) n++;\n"
                 "  initial #41 $display(\"n=%0d\", n);\n"
                 "endprogram\n"
                 "module t;\n"
                 "  logic cs[2] = '{0, 0};\n"
                 "  always #5 cs[0] = ~cs[0];\n"
                 "  p u(cs);\n"
                 "  initial #45 $finish;\n"
                 "endmodule\n",
                 f),
      "n=3\n$finish at time 45\n");
}

}  // namespace
