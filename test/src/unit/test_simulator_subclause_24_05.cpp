#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BlockingTasksCycleEventMode,
     ModuleTaskCalledFromModuleBlockingRunsInActive) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  task write_v(input logic [7:0] val);\n"
      "    v = val;\n"
      "  endtask\n"
      "  initial v <= 8'd10;\n"
      "  initial write_v(8'd99);\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

TEST(BlockingTasksCycleEventMode,
     ModuleTaskCalledFromProgramBlockingRunsInReactive) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  task write_v(input logic [7:0] val);\n"
      "    v = val;\n"
      "  endtask\n"
      "  initial v <= 8'd10;\n"
      "  program p;\n"
      "    initial write_v(8'd99);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(BlockingTasksCycleEventMode,
     ModuleTaskNonBlockingCalledFromProgramCommitsInReNba) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  task nba_copy;\n"
      "    b <= a;\n"
      "  endtask\n"
      "  initial a <= 8'd42;\n"
      "  program p;\n"
      "    initial nba_copy();\n"
      "  endprogram\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 42u);
}

TEST(BlockingTasksCycleEventMode, ModuleFunctionCalledFromProgramReturnsValue) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module top;\n"
      "  int r;\n"
      "  function automatic int add_one(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  program p;\n"
      "    initial r = add_one(41);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 42u);
}

// §24.5 (printed page 778) with §23.6 (printed page 753): a program may enable
// a design module's task by hierarchical name, and the task runs in the
// program's thread, its delays consumed before the program goes on. Written
// without its empty parentheses (§13.5.5), `top.T;` is that enable too.
TEST(BlockingTasksCycleEventMode,
     ModuleTaskEnabledByHierarchicalNameFromProgramRunsItsBody) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int a = 1, b = 2;\n"
                       "  task T;\n"
                       "    a = b;\n"
                       "    $display(\"T a=%0d at %0t\", a, $time);\n"
                       "    #5 b <= 7;\n"
                       "    #1 $display(\"T b=%0d at %0t\", b, $time);\n"
                       "  endtask\n"
                       "  initial #10 b = 5;\n"
                       "  p pi();\n"
                       "endmodule\n"
                       "program p;\n"
                       "  initial begin\n"
                       "    #10 top.T;\n"
                       "    $display(\"prog done at %0t\", $time);\n"
                       "  end\n"
                       "endprogram\n",
                       f),
            "T a=5 at 10\nT b=7 at 16\nprog done at 16\n");
}

// The same enable from a submodule, beside a function called upward.
TEST(BlockingTasksCycleEventMode,
     ModuleTaskEnabledByHierarchicalNameFromSubmoduleRunsItsBody) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module sub;\n"
                 "  initial begin\n"
                 "    #1 $display(\"sub f=%0d at %0t\", top.scale(7), $time);\n"
                 "    top.T;\n"
                 "  end\n"
                 "endmodule\n"
                 "module top;\n"
                 "  int k = 5, a = 1, b = 2;\n"
                 "  function int scale(int x); return x * k; endfunction\n"
                 "  task T; a = b; $display(\"T a=%0d at %0t\", a, $time); "
                 "endtask\n"
                 "  sub s();\n"
                 "endmodule\n",
                 f),
      "sub f=35 at 1\nT a=2 at 1\n");
}

// §24.5 with §23.6: a program calls a sibling instance's function through the
// top's name, and another program's task, whose delay it waits out.
TEST(BlockingTasksCycleEventMode,
     ProgramCallsThroughTheTopNameIntoInstancesAndPrograms) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module dut;\n"
                 "  int k = 5;\n"
                 "  function int scale(int x); return x * k; endfunction\n"
                 "endmodule\n"
                 "module top;\n"
                 "  dut d();\n"
                 "  p pi();\n"
                 "endmodule\n"
                 "program p;\n"
                 "  initial #1 $display(\"prog f=%0d at %0t\", top.d.scale(7), "
                 "$time);\n"
                 "endprogram\n",
                 f),
      "prog f=35 at 1\n");
  SimFixture g;
  EXPECT_EQ(RunCapture("program helper;\n"
                       "  int v = 12;\n"
                       "  task wait_for(int d);\n"
                       "    #d $display(\"helper d=%0d at %0t\", d, $time);\n"
                       "  endtask\n"
                       "endprogram\n"
                       "program user;\n"
                       "  initial begin\n"
                       "    top.h.wait_for(4);\n"
                       "    $display(\"user v=%0d at %0t\", top.h.v, $time);\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  helper h(); user u();\n"
                       "endmodule\n",
                       g),
            "helper d=4 at 4\nuser v=12 at 4\n");
}

}  // namespace
