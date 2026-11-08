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

TEST(ProgramConstructSim, ModuleAutomaticGivesATaskAnActivationPerCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture(RecursiveTaskUnder("module automatic top;\n", "task",
                                          "endmodule\n"),
                       f),
            "k=0 k=1 k=2\n");
}

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

TEST(ProgramConstructSim, ExternProgramDefinitionRunsWithPrototypePorts) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "extern program p(input var int v, output int w);\n"
      "program p(.*);\n"
      "  initial #1 w = v + 1;\n"
      "endprogram\n"
      "module top;\n"
      "  int v = 57;\n"
      "  int w;\n"
      "  p pi(v, w);\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.ToUint64(), 58u);
}

TEST(ProgramConstructSim, ProgramNestedInAnInterfaceReadsItsVariable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface Bus;\n"
                 "  int a;\n"
                 "  program p;\n"
                 "    initial #1 $display(\"%m a=%0d at %0t\", a, $time);\n"
                 "  endprogram\n"
                 "endinterface\n"
                 "module top;\n"
                 "  Bus s();\n"
                 "  initial s.a = 71;\n"
                 "endmodule\n",
                 f),
      "top.s.p a=71 at 1\n");
}

TEST(ProgramConstructSim, ProgramNestedInAnInterfaceReadsItsPortAndVariable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface Bus(input logic clk);\n"
                 "  int a;\n"
                 "  initial a = 71;\n"
                 "  program p;\n"
                 "    initial #1 $display(\"%m clk=%b a=%0d at %0t\", clk, a,\n"
                 "                        $time);\n"
                 "  endprogram\n"
                 "endinterface\n"
                 "module top;\n"
                 "  logic clk = 1;\n"
                 "  Bus s(clk);\n"
                 "endmodule\n",
                 f),
      "top.s.p clk=1 a=71 at 1\n");
}

}  // namespace
