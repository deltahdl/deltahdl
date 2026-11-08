#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TaskAndFunctionNameResolutionSimulation,
     CuScopeFunctionReturnsValueWhenCalledFromModule) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "function int cu_add(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n"
      "module m;\n"
      "  integer x;\n"
      "  initial x = cu_add(4, 5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 9u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     CuScopeTaskExecutesWhenCalledFromModule) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "task cu_set(output int v);\n"
      "  v = 1;\n"
      "endtask\n"
      "module m;\n"
      "  int x;\n"
      "  initial cu_set(x);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     TaskBodyResolvesBareCallToCompilationUnitFunction) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "function int f(int y);\n"
      "  return y + 1;\n"
      "endfunction\n"
      "module m;\n"
      "  integer r;\n"
      "  task t;\n"
      "    r = f(1);\n"
      "  endtask\n"
      "  initial t();\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 2u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     ModuleLocalFunctionTakesPrecedenceOverCompilationUnit) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "function int f(int a);\n"
      "  return a + 100;\n"
      "endfunction\n"
      "module m;\n"
      "  function int f(int a);\n"
      "    return a;\n"
      "  endfunction\n"
      "  integer x;\n"
      "  initial x = f(7);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 7u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     CuScopeFunctionResolvesAcrossMultipleHierarchyLevels) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "function int cu_id(int a);\n"
      "  return a;\n"
      "endfunction\n"
      "module leaf;\n"
      "  integer x;\n"
      "  initial x = cu_id(42);\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "endmodule\n",
      f, "m1.l1.x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     CuScopeFunctionResolvesFromSiblingModuleInstances) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "function int cu_double(int a);\n"
      "  return a * 2;\n"
      "endfunction\n"
      "module child;\n"
      "  integer x;\n"
      "  initial x = cu_double(3);\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  child c2();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v1 = f.ctx.FindVariable("c1.x");
  auto* v2 = f.ctx.FindVariable("c2.x");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 6u);
  EXPECT_EQ(v2->value.ToUint64(), 6u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     CuScopeFunctionResolvesBareCallInsideAnotherCuFunction) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "function int cu_inner(int a);\n"
      "  return a + 1;\n"
      "endfunction\n"
      "function int cu_outer(int a);\n"
      "  return cu_inner(a) + 10;\n"
      "endfunction\n"
      "module m;\n"
      "  integer x;\n"
      "  initial x = cu_outer(5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 16u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     ForwardDefinedCompilationUnitFunctionResolvesAndExecutes) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  integer x;\n"
      "  initial x = later_add(4, 5);\n"
      "endmodule\n"
      "function int later_add(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 9u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     ForwardDefinedCompilationUnitTaskResolvesAndExecutes) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  int x;\n"
      "  initial later_set(x);\n"
      "endmodule\n"
      "task later_set(output int v);\n"
      "  v = 42;\n"
      "endtask\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     CompilationUnitFunctionBodyCallsForwardDefinedCompilationUnitFunction) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "function int caller(int a);\n"
      "  return f(a) + 100;\n"
      "endfunction\n"
      "module m;\n"
      "  integer x;\n"
      "  initial x = caller(10);\n"
      "endmodule\n"
      "function int f(int y);\n"
      "  return y + 1;\n"
      "endfunction\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 111u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     UnitTaskCallFromGenerateBlockReachesTheUnitFunction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  function void f();\n"
                       "    $display(\"p::f\");\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "task t;\n"
                       "  int x;\n"
                       "  x = f(1);\n"
                       "  $display(\"%0d\", x);\n"
                       "endtask\n"
                       "function int f(int y);\n"
                       "  return y + 1;\n"
                       "endfunction\n"
                       "module top;\n"
                       "  import p::*;\n"
                       "  if (1) begin : b\n"
                       "    initial begin f(); #1 t(); end\n"
                       "    function void f();\n"
                       "      $display(\"top.b.f\");\n"
                       "    endfunction\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "top.b.f\n2\n");
}

TEST(TaskAndFunctionNameResolutionSimulation,
     UnitTaskCallReachesTheUnitFunctionAheadOfTheCallersOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("task t;\n"
                       "  $display(\"%0d\", f(1));\n"
                       "endtask\n"
                       "function int f(int y);\n"
                       "  return y + 1;\n"
                       "endfunction\n"
                       "module top;\n"
                       "  function int f(int y);\n"
                       "    return y + 100;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    $display(\"%0d\", f(1));\n"
                       "    t();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "101\n2\n");
}

TEST(TaskAndFunctionNameResolutionSimulation,
     TopsBareCallRunsItsOwnTaskAheadOfAnInstancesOfTheSameName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  task t; $display(\"child.t\"); endtask\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child c();\n"
                       "  task t; $display(\"top.t\"); endtask\n"
                       "  initial t();\n"
                       "endmodule\n",
                       f),
            "top.t\n");
}

TEST(TaskAndFunctionNameResolutionSimulation,
     TopsBareCallRunsTheUnitsFunctionAheadOfAnInstancesOfTheSameName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("function void f; $display(\"unit.f\"); endfunction\n"
                       "module child;\n"
                       "  function void f; $display(\"child.f\"); endfunction\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child c();\n"
                       "  initial f();\n"
                       "endmodule\n",
                       f),
            "unit.f\n");
}

}  // namespace
