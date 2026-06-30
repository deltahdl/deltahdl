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

// A program initial's event control on a design signal resumes in the Reactive
// region (24.3.1): when trig transitions, the program statement is scheduled
// into the Reactive region, after the design's NBA region has committed v<=10,
// so the program-driven v=99 wins. The design drives trig one time step later
// (#1) because a program initial executes in the Reactive region (24.3.1),
// strictly after the Active region of the same time slot; were trig driven at
// time 0 the program's @(trig) would not yet be armed when the design's Active
// write occurred, a clocking-block-less program/design race (24.3.2). Delaying
// the design write lets the program arm @(trig) first, so the resume is
// deterministic and exercises the Reactive-region scheduling under test.
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
      "    #1 trig = 1'b1;\n"
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

// A subroutine declared outside the program (here in the enclosing module)
// inherits the reactive scheduling region of the program thread that calls it.
// The task's blocking write therefore lands in the Reactive region, after the
// design's NBA region has committed, so the program-driven value wins.
TEST(ProgramSchedulingSim, ModuleTaskCalledFromProgramRunsBlockingInReactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  task set_v;\n"
      "    v = 8'd99;\n"
      "  endtask\n"
      "  initial v <= 8'd10;\n"
      "  program p;\n"
      "    initial set_v();\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

// The same inheritance applies to nonblocking assignments: an NBA executed
// inside a module-declared subroutine that is called from a program thread is
// scheduled in the Re-NBA region, which runs after the design NBA region, so
// the subroutine reads the design's already-committed value.
TEST(ProgramSchedulingSim, ModuleTaskCalledFromProgramSchedulesNbaInReactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  task do_nba;\n"
      "    b <= a;\n"
      "  endtask\n"
      "  initial a <= 8'd10;\n"
      "  program p;\n"
      "    initial do_nba();\n"
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

// Concurrent assertions keep their invariant scheduling inside a program: they
// are still sampled and evaluated in the Observed region rather than skipped
// because the code lives in program scope. With the same structure as the
// passing case but a predicate that does not hold, the assertion must actually
// fire, proving production evaluates it instead of silently ignoring it.
TEST(ProgramSchedulingSim, ConcurrentAssertionInProgramStillEvaluatesAndFails) {
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
      "    assert property (@(posedge clk) x == 8'd2);\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

}  // namespace
