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

TEST(ProgramPortConnectionSim, DesignAlwaysSensitiveToProgramWriteObservesUpdate) {
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

TEST(ProgramPortConnectionSim, ProgramAssignTriggersDesignAlwaysOnNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic r;\n"
      "  wire  dw;\n"
      "  logic captured;\n"
      "  initial begin\n"
      "    captured = 1'b0;\n"
      "    r = 1'b0;\n"
      "    #1 r = 1'b1;\n"
      "  end\n"
      "  always @(dw) captured = dw;\n"
      "  program p;\n"
      "    assign dw = r;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* cap = f.ctx.FindVariable("captured");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->value.ToUint64(), 1u);
}

TEST(ProgramPortConnectionSim, ProgramNbaToDesignVariableCommitsInReNba) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial a <= 8'd9;\n"
      "  program p;\n"
      "    initial b <= a;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 9u);
}

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

TEST(ProgramPortConnectionSim, DesignWriteVisibleInProgramRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] from_design;\n"
      "  logic [7:0] inside_program;\n"
      "  initial from_design <= 8'd123;\n"
      "  program p;\n"
      "    initial inside_program = from_design;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* inside = f.ctx.FindVariable("inside_program");
  ASSERT_NE(inside, nullptr);
  EXPECT_EQ(inside->value.ToUint64(), 123u);
}

TEST(ProgramPortConnectionSim, UnchangedSignalDoesNotTriggerDesignProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] shared;\n"
      "  logic [7:0] hits;\n"
      "  initial begin\n"
      "    hits = 8'd0;\n"
      "    shared = 8'd5;\n"
      "  end\n"
      "  always @(shared) hits = hits + 8'd1;\n"
      "  program p;\n"
      "    initial #1 shared = 8'd5;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* hits = f.ctx.FindVariable("hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_LE(hits->value.ToUint64(), 1u);
}

TEST(ProgramPortConnectionSim, ProgramDrivesWireChainIntoDesignAlways) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] src;\n"
      "  wire  [7:0] mid;\n"
      "  wire  [7:0] last;\n"
      "  logic [7:0] observed;\n"
      "  assign last = mid;\n"
      "  initial begin\n"
      "    observed = 8'd0;\n"
      "    src = 8'd0;\n"
      "    #1 src <= 8'd64;\n"
      "  end\n"
      "  always @(last) observed = last;\n"
      "  program p;\n"
      "    assign mid = src;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* obs = f.ctx.FindVariable("observed");
  ASSERT_NE(obs, nullptr);
  EXPECT_EQ(obs->value.ToUint64(), 64u);
}

}  // namespace
