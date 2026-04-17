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

}  // namespace
