#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ProgramConstructSim, NestedProgramInitialRuns) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  program p;\n"
      "    initial v = 8'd42;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(ProgramConstructSim, ImplicitFinishAfterProgramInitialCompletes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] x;\n"
      "  program p;\n"
      "    initial x = 8'd1;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.ctx.StopRequested());
}

TEST(ProgramConstructSim, NoImplicitFinishWithoutProgramInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] y;\n"
      "  initial y = 8'd5;\n"
      "  program p;\n"
      "    int z;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.ctx.StopRequested());
}

// §24.3: the implicit $finish fires "immediately after all the threads ...
// within all programs have ended" -- not when the first one ends. Two program
// blocks whose initials complete at different times (t=20 and t=60) must both
// run to completion before the run stops. If the stop fired when the earlier
// initial (p1) ended at t=20, p2's #60 delay would be cut off and b would keep
// its reset value; observing b==2 shows the run waited for the latest-ending
// program initial across both blocks.
TEST(ProgramConstructSim,
     ImplicitFinishWaitsForLatestProgramInitialAcrossBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  program p1;\n"
      "    initial begin #20 a = 8'd1; end\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial begin #60 b = 8'd2; end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.ctx.StopRequested());
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 1u);
  EXPECT_EQ(b->value.ToUint64(), 2u);
}

TEST(ProgramConstructSim, ProgramInitialTerminatesDescendantThreads) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  program p;\n"
      "    initial begin\n"
      "      fork\n"
      "        begin\n"
      "          #100 v = 8'd99;\n"
      "        end\n"
      "      join_none\n"
      "      v = 8'd7;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 7u);
}

// §24.3: a top-level program not explicitly instantiated is implicitly
// instantiated once (printed page 776 of ~/IEEE 1800-2023.pdf), so its initial
// runs and a task it declares, enabled from that initial, consumes its delay
// (§13.3): the write lands at time 5. The program was rooted by no run before,
// so nothing ran and `at` kept its reset value.
TEST(ProgramConstructSim, ATopLevelProgramsInitialRunsItsTask) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  int at;\n"
      "  task pw(int d); #d; at = d * 100 + $time; endtask\n"
      "  initial pw(5);\n"
      "endprogram\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* at = f.ctx.FindVariable("at");
  ASSERT_NE(at, nullptr);
  EXPECT_EQ(at->value.ToUint64(), 505u);
}

// The same beside a module: both tops run, the module's initial and the
// program's, so the unit is elaborated with no top named.
TEST(ProgramConstructSim, ATopLevelProgramBesideAModuleRunsWithIt) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "module t;\n"
      "  int a;\n"
      "  initial a = 3;\n"
      "endmodule\n"
      "program p;\n"
      "  int b;\n"
      "  initial b = 7;\n"
      "endprogram\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 3u);
  EXPECT_EQ(b->value.ToUint64(), 7u);
}

}  // namespace
