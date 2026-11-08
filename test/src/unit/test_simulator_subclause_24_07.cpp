#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ProgramControlTasksSim, ExitFromProgramInitialRequestsStop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    initial $exit();\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

TEST(ProgramControlTasksSim, ExitSkipsSubsequentStatementsInProgramInitial) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p;\n"
      "    initial begin\n"
      "      $exit();\n"
      "      v = 8'd99;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

TEST(ProgramControlTasksSim, ExitTerminatesPeerProgramInitial) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p;\n"
      "    initial $exit();\n"
      "    initial begin\n"
      "      #100 v = 8'd77;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

TEST(ProgramControlTasksSim, ExitFromForkedDescendantTerminatesProgramInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p;\n"
      "    initial begin\n"
      "      fork\n"
      "        $exit();\n"
      "      join\n"
      "      v = 8'd55;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.StopRequested());
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

TEST(ProgramControlTasksSim, ExitFromModuleInitialIsIgnored) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    $exit();\n"
      "    v = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
  EXPECT_FALSE(f.ctx.StopRequested());
}

TEST(ProgramControlTasksSim, ExitFromModuleAlwaysIsIgnored) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    v = 8'd0;\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 v = 8'd7;\n"
      "  end\n"
      "  always @(posedge clk) $exit();\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 7u);
}

TEST(ProgramControlTasksSim, ExitDoesNotTerminateOtherProgramBlock) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p1;\n"
      "    initial $exit();\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial v = 8'd33;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 33u);
}

TEST(ProgramControlTasksSim, ExitWithoutParensTerminatesProgramInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p;\n"
      "    initial begin\n"
      "      $exit;\n"
      "      v = 8'd88;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.StopRequested());
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

TEST(ProgramControlTasksSim, ExitFromForkedDescendantInModuleIsIgnored) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'd0;\n"
      "    fork\n"
      "      $exit();\n"
      "    join\n"
      "    v = 8'd44;\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 44u);
}

TEST(ProgramControlTasksSim, ExitFromTaskCalledInProgramInitialTerminates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p;\n"
      "    task do_exit;\n"
      "      $exit();\n"
      "    endtask\n"
      "    initial begin\n"
      "      do_exit();\n"
      "      v = 8'd66;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.StopRequested());
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

TEST(ProgramControlTasksSim, ExitInsideProgramTaskEndsTheRestOfTheTask) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program p;\n"
                 "  task automatic run();\n"
                 "    #3 $display(\"task exits at %0t\", $time);\n"
                 "    $exit;\n"
                 "    $display(\"after in task\");\n"
                 "  endtask\n"
                 "  initial begin run(); $display(\"after in initial\"); end\n"
                 "endprogram\n"
                 "module top; p pi(); endmodule\n",
                 f),
      "task exits at 3\n");
}

TEST(ProgramControlTasksSim, ExitInsideClassTaskEndsTheRestOfTheTask) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Q;\n"
                       "  task run();\n"
                       "    #3 $display(\"class task exits at %0t\", $time);\n"
                       "    $exit;\n"
                       "    $display(\"after in task\");\n"
                       "  endtask\n"
                       "endclass\n"
                       "program p;\n"
                       "  initial begin\n"
                       "    automatic Q q = new;\n"
                       "    q.run();\n"
                       "    $display(\"after in initial\");\n"
                       "  end\n"
                       "endprogram\n"
                       "module top; p pi(); endmodule\n",
                       f),
            "class task exits at 3\n");
}

TEST(ProgramControlTasksSim, ExitFromForkChildEndsTheRunAtItsTime) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n"
                       "  initial begin\n"
                       "    fork\n"
                       "      begin #2 $display(\"child exits at %0t\", $time);"
                       " $exit; end\n"
                       "      begin #5 $display(\"sibling\"); end\n"
                       "    join\n"
                       "    $display(\"parent after join\");\n"
                       "  end\n"
                       "  initial #9 $display(\"other initial\");\n"
                       "endprogram\n"
                       "module top; p pi(); endmodule\n",
                       f),
            "child exits at 2\n");
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 2u);
}

TEST(ProgramControlTasksSim, ExitInForeverLoopEndsTheRunAtTheEdge) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  p pi(clk);\n"
                       "endmodule\n"
                       "program p(input logic clk);\n"
                       "  int n = 0;\n"
                       "  initial forever @(posedge clk) begin\n"
                       "    n++;\n"
                       "    if (n == 3) begin\n"
                       "      $display(\"exit at %0t\", $time);\n"
                       "      $exit;\n"
                       "    end\n"
                       "  end\n"
                       "endprogram\n",
                       f),
            "exit at 25\n");
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 25u);
}

TEST(ProgramControlTasksSim,
     ExitFromModuleInitialBesideRunningProgramIsIgnored) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program pr;\n"
                       "  initial #30 $display(\"prog %0t\", $time);\n"
                       "endprogram\n"
                       "module t;\n"
                       "  pr p1();\n"
                       "  initial begin\n"
                       "    #3 $display(\"mod %0t\", $time);\n"
                       "    $exit;\n"
                       "    #10 $display(\"after exit %0t\", $time);\n"
                       "  end\n"
                       "  initial #40 $display(\"past the program\");\n"
                       "endmodule\n",
                       f),
            "mod 3\nafter exit 13\nprog 30\n");
}

TEST(ProgramControlTasksSim, ProgramEndBeforeModuleExitEndsTheRun) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program pr;\n"
                       "  initial #2 $display(\"prog %0t\", $time);\n"
                       "endprogram\n"
                       "module t;\n"
                       "  pr p1();\n"
                       "  initial begin\n"
                       "    #3 $display(\"mod %0t\", $time);\n"
                       "    $exit;\n"
                       "    #10 $display(\"never\");\n"
                       "  end\n"
                       "  initial #20 $display(\"never2\");\n"
                       "endmodule\n",
                       f),
            "prog 2\n");
}

TEST(ProgramControlTasksSim, ExitWithNoProgramIsIgnored) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial begin\n"
                       "    $display(\"a\");\n"
                       "    $exit;\n"
                       "    $display(\"b\");\n"
                       "  end\n"
                       "  initial #2 $display(\"c\");\n"
                       "endmodule\n",
                       f),
            "a\nb\nc\n");
}

TEST(ProgramControlTasksSim, ExitLeavesAnotherProgramsDelayedInitialRunning) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p1;\n"
      "    initial $exit();\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial #5 v = 8'd33;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 33u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 5u);
}

}  // namespace
