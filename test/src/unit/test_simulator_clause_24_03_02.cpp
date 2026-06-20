#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
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
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] src;\n"
      "  wire  [7:0] dnet;\n"
      "  initial src <= 8'd55;\n"
      "  program p;\n"
      "    assign dnet = src;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dnet = f.ctx.FindVariable("dnet");
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
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] crossed;\n"
      "  logic [7:0] observed;\n"
      "  initial observed = 8'd0;\n"
      "  always @(crossed) observed = crossed;\n"
      "  program p;\n"
      "    initial #1 crossed = 8'd77;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* obs = f.ctx.FindVariable("observed");
  ASSERT_NE(obs, nullptr);
  EXPECT_EQ(obs->value.ToUint64(), 77u);
}

// §24.3.2: driving and resolution of a net happen right after an event changes
// a driver on a program net. A design process that samples the resolved net at
// a later time step must see the value produced by the program's
// reactive-region drive.
TEST(ProgramPortConnectionSim, NetResolutionImmediateOnProgramDriverChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* s = f.ctx.FindVariable("sampled");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* hits = f.ctx.FindVariable("hits");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* cap = f.ctx.FindVariable("captured");
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
  auto* design = ElaborateSrc(
      "program p(input [7:0] din, output logic [7:0] dout);\n"
      "  assign dout = din;\n"
      "endprogram\n"
      "module top;\n"
      "  logic [7:0] feed;\n"
      "  logic [7:0] catch_var;\n"
      "  initial feed <= 8'd200;\n"
      "  p p_i(.din(feed), .dout(catch_var));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* cv = f.ctx.FindVariable("catch_var");
  ASSERT_NE(cv, nullptr);
  EXPECT_EQ(cv->value.ToUint64(), 200u);
}

}  // namespace
