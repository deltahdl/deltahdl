#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TaskAndFunctionNameResolutionSimulation,
     CuScopeFunctionReturnsValueWhenCalledFromModule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "function int cu_add(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n"
      "module m;\n"
      "  integer x;\n"
      "  initial x = cu_add(4, 5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 9u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     CuScopeTaskExecutesWhenCalledFromModule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "task cu_set(output int v);\n"
      "  v = 1;\n"
      "endtask\n"
      "module m;\n"
      "  int x;\n"
      "  initial cu_set(x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     TaskBodyResolvesBareCallToCompilationUnitFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 2u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     ModuleLocalFunctionTakesPrecedenceOverCompilationUnit) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 7u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     CuScopeFunctionResolvesAcrossMultipleHierarchyLevels) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("m1.l1.x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(TaskAndFunctionNameResolutionSimulation,
     CuScopeFunctionResolvesFromSiblingModuleInstances) {
  SimFixture f;
  // The single compilation-unit function serves every bare reference; two
  // independent instances each resolve and execute it.
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
  // The compilation-unit lookup also applies to a bare reference made from
  // within a compilation-unit subroutine body, not only from module bodies.
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 16u);
}

}  // namespace
