#include <gtest/gtest.h>

#include <string>

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
// instantiated once (printed page 776 of IEEE 1800-2023), so its initial
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
  auto* b = f.ctx.FindVariable("p.b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 3u);
  EXPECT_EQ(b->value.ToUint64(), 7u);
}

// A recursive task that records its local after the inner calls return, so
// each activation's `k` shows whether it was its own or a shared one.
std::string RecursiveTaskUnder(const std::string& header,
                               const std::string& task_kw,
                               const std::string& footer) {
  return header +
         "  string s;\n"
         "  " +
         task_kw +
         " rec(int n);\n"
         "    int k;\n"
         "    k = n;\n"
         "    if (n > 0) rec(n - 1);\n"
         "    s = {s, $sformatf(\"k=%0d\", k), (n == 2) ? \"\" : \" \"};\n"
         "  endtask\n"
         "  initial begin rec(2); $display(\"%s\", s); end\n" +
         footer;
}

// §24.3 Syntax 24-1 (printed page 775) with §6.21 (printed page 132) and
// §13.3.1: a program's lifetime qualifier is the default lifetime of the
// subroutines declared in it, so under `program automatic` each activation of
// a recursive task has its own local, and under `program static` all share
// one. A `task automatic` in a program with no qualifier is automatic too.
TEST(ProgramConstructSim, ProgramLifetimeIsTheDefaultOfItsTasks) {
  const std::string kTop = "endprogram\nmodule top; p pi(); endmodule\n";
  SimFixture fa;
  EXPECT_EQ(RunCapture(
                RecursiveTaskUnder("program automatic p;\n", "task", kTop), fa),
            "k=0 k=1 k=2\n");
  SimFixture fs;
  EXPECT_EQ(
      RunCapture(RecursiveTaskUnder("program static p;\n", "task", kTop), fs),
      "k=0 k=0 k=0 \n");
  SimFixture ft;
  EXPECT_EQ(RunCapture(
                RecursiveTaskUnder("program p;\n", "task automatic", kTop), ft),
            "k=0 k=1 k=2\n");
}

// §23.2.1 (printed page 728): the same default taken from `module automatic`.
TEST(ProgramConstructSim, ModuleAutomaticGivesATaskAnActivationPerCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture(RecursiveTaskUnder("module automatic top;\n", "task",
                                          "endmodule\n"),
                       f),
            "k=0 k=1 k=2\n");
}

// §24.3 (printed page 776) with §7.2 (printed page 146) and §7.8 (printed
// page 163): a struct and an associative array declared as program items are
// variables of the program instance, so their member and key writes are kept
// and read back beside a queue's pushes.
TEST(ProgramConstructSim, StructQueueAndAssociativeProgramVariablesHoldWrites) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program p;\n"
                 "  typedef struct { int a; int b; } pair_t;\n"
                 "  pair_t st;\n"
                 "  int q[$];\n"
                 "  int aa[string];\n"
                 "  initial begin\n"
                 "    st.a = 6; st.b = 7;\n"
                 "    q.push_back(10); q.push_back(20); q.push_back(30);\n"
                 "    aa[\"x\"] = 44; aa[\"y\"] = 55;\n"
                 "    $display(\"st=%0d q=%0d sum=%0d aa=%0d v=%0d\", "
                 "st.a + st.b, q.size(), q[0] + q[1] + q[2], aa.num(), "
                 "aa[\"x\"]);\n"
                 "  end\n"
                 "endprogram\n"
                 "module top; p pi(); endmodule\n",
                 f),
      "st=13 q=3 sum=60 aa=2 v=44\n");
}

// §24.3 (printed page 776) with §6.19.5.3 (printed page 123) and §6.19.5.6
// (printed page 124): an enum typedef declared as a program item names its
// literals in the program's scope, so a program variable and a local of the
// initial's block of the type store the literal's value and answer `name()`
// and `next()` on it. The program variable's methods answered nothing, and
// the block local stored nothing at all.
TEST(ProgramConstructSim, EnumTypedefProgramItemAnswersItsMethods) {
  const std::string kEnum =
      "program p;\n"
      "  typedef enum { RED, GREEN, BLUE } color_t;\n";
  const std::string kShow =
      "$display(\"prog s=%s n=%0d next=%s\", s.name(), s, "
      "s.next().name()); end\n"
      "endprogram\n"
      "module top; p pi(); endmodule\n";
  SimFixture fv;
  EXPECT_EQ(
      RunCapture(kEnum + "  color_t s;\n  initial begin s = GREEN; " + kShow,
                 fv),
      "prog s=GREEN n=1 next=BLUE\n");
  SimFixture fl;
  EXPECT_EQ(
      RunCapture(kEnum + "  initial begin color_t s; s = GREEN; " + kShow, fl),
      "prog s=GREEN n=1 next=BLUE\n");
}

// §24.3: once every initial procedure of every program has ended, the run
// ends at once through an implicit $finish, so a module initial waiting past
// that time never runs its statement and the run stops at the program's end.
TEST(ProgramConstructSim, ProgramEndEndsTheRunBeforeLaterDesignEvents) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n"
                       "  initial #2 $display(\"prog at %0t\", $time);\n"
                       "endprogram\n"
                       "module top;\n"
                       "  p pi();\n"
                       "  initial #9 $display(\"mod at 9\");\n"
                       "endmodule\n",
                       f),
            "prog at 2\n");
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 2u);
}

// §24.3 as above beside a free-running design clock, whose next toggle is
// no reason to go on: the run still ends at 2.
TEST(ProgramConstructSim, ProgramEndEndsTheRunBesideAFreeRunningClock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n"
                       "  initial #2 $display(\"prog at %0t\", $time);\n"
                       "endprogram\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  p pi();\n"
                       "  initial #9 $display(\"mod at 9\");\n"
                       "endmodule\n",
                       f),
            "prog at 2\n");
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 2u);
}

// §24.3 with §9.3.2: after join_any the initial runs to its end at 1, which
// ends the sibling still pending and the run with it.
TEST(ProgramConstructSim, ProgramEndAfterJoinAnyEndsTheRun) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n"
                       "  initial begin\n"
                       "    fork\n"
                       "      #1 $display(\"fast at %0t\", $time);\n"
                       "      #6 $display(\"slow\");\n"
                       "    join_any\n"
                       "    $display(\"parent at %0t\", $time);\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  p pi();\n"
                       "  initial #9 $display(\"mod at 9\");\n"
                       "endmodule\n",
                       f),
            "fast at 1\nparent at 1\n");
}

// §24.3: with an input port connected and driven by the module after the
// program's end, the program's end at 4 still ends the run there.
TEST(ProgramConstructSim, ProgramWithDrivenInputPortEndsTheRunAtItsEnd) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p(input logic d);\n"
                       "  initial #4 $display(\"prog end at %0t\", $time);\n"
                       "endprogram\n"
                       "module top;\n"
                       "  logic d = 0;\n"
                       "  p pi(d);\n"
                       "  initial begin #5 d = 1; $display(\"mod at 5\"); end\n"
                       "endmodule\n",
                       f),
            "prog end at 4\n");
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 4u);
}

// §24.3 with §4.4.2: a program's initial procedure runs in the Reactive
// region, so at one time it runs after a module's, which runs in the Active
// region, whatever time unit either reads its delay in.
TEST(ProgramSim, AProgramInitialRunsAfterAModuleInitialAtOneTime) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  timeunit 1ps / 1ps;\n"
                       "  pr p();\n"
                       "  initial #2000 $display(\"mod %0d\", $time);\n"
                       "endmodule\n"
                       "program pr;\n"
                       "  timeunit 1ns / 1ps;\n"
                       "  initial #2 $display(\"prog %0d %f\", $time, "
                       "$realtime);\n"
                       "endprogram\n",
                       f),
            "mod 2000\nprog 2 2.000000\n");
}

// §24.3 with §23.10.2: a program nested in a module is instantiated in each
// instance of the module and reads the module's parameter at the value that
// instance gives it. m1's K is 7 and m2's 2, and the delays order the lines.
// The program's lookup fell back to the top's storage, which holds no K, and
// both lines read 0.
TEST(ProgramConstructSim, NestedProgramReadsItsModuleInstanceParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter int K = 0);\n"
                       "  program p;\n"
                       "    initial #K $display(\"k=%0d\", K);\n"
                       "  endprogram\n"
                       "endmodule\n"
                       "module top;\n"
                       "  m #(7) m1();\n"
                       "  m #(2) m2();\n"
                       "endmodule\n",
                       f),
            "k=2\nk=7\n");
}

}  // namespace
