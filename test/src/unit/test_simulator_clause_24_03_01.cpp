#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ProgramSim, ReactiveContextFlag) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  EXPECT_FALSE(ctx.IsReactiveContext());

  Process proc;
  proc.is_reactive = true;
  ctx.SetCurrentProcess(&proc);
  EXPECT_TRUE(ctx.IsReactiveContext());

  Process non_reactive;
  non_reactive.is_reactive = false;
  ctx.SetCurrentProcess(&non_reactive);
  EXPECT_FALSE(ctx.IsReactiveContext());

  ctx.SetCurrentProcess(nullptr);
}

TEST(ProgramSchedulingSim, ProgramInitialRunsAfterDesignNba) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v <= 8'd10;\n"
      "  program p;\n"
      "    initial v = 8'd99;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(ProgramSchedulingSim, ProgramInitialRunsAfterDesignActiveInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'd1;\n"
      "    v <= 8'd10;\n"
      "  end\n"
      "  program p;\n"
      "    initial v = 8'd99;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(ProgramSchedulingSim, ProgramContinuousAssignPropagatesReactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial a <= 8'd77;\n"
      "  program p;\n"
      "    assign b = a;\n"
      "    initial ;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 77u);
}

TEST(ProgramSchedulingSim, ProgramDelayResumesInReactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial #5 v <= 8'd10;\n"
      "  program p;\n"
      "    initial #5 v = 8'd99;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(ProgramSchedulingSim, ProgramNbaCommitsAfterDesignNba) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial a <= 8'd10;\n"
      "  program p;\n"
      "    initial b <= a;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(b->value.ToUint64(), 10u);
}

TEST(ProgramSchedulingSim, ProgramEventWaitResumesInReactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  logic trig;\n"
      "  program p;\n"
      "    initial @(trig) v = 8'd99;\n"
      "  endprogram\n"
      "  initial begin\n"
      "    trig = 1'b1;\n"
      "    v <= 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(ProgramSchedulingSim, MultipleProgramInitialsEachRunInReactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial a <= 8'd1;\n"
      "  initial b <= 8'd2;\n"
      "  program p;\n"
      "    initial a = 8'd100;\n"
      "    initial b = 8'd200;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 100u);
  EXPECT_EQ(b->value.ToUint64(), 200u);
}

TEST(ProgramSchedulingSim, ConcurrentAssertionInProgramRunsWithoutCrash) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  program p;\n"
      "    initial begin\n"
      "      x = 8'd1;\n"
      "      #5 ;\n"
      "    end\n"
      "    initial begin\n"
      "      clk = 1'b0;\n"
      "      #1 clk = 1'b1;\n"
      "    end\n"
      "    assert property (@(posedge clk) x == 8'd1);\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.StopRequested());
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
}

}  // namespace
