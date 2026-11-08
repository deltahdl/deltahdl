#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(TaskDeclSim, StaticTaskVarsPersist) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task static counter(output logic [31:0] v);\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    v = cnt;\n"
      "  endtask\n"
      "  initial begin\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(TaskDeclSim, AutomaticTaskVarsFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task automatic counter(output logic [31:0] v);\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    v = cnt;\n"
      "  endtask\n"
      "  initial begin\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "  end\n"
      "endmodule\n",
      "result");

  EXPECT_EQ(val, 1u);
}

TEST(TaskDeclSim, DefaultTaskIsStatic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task counter(output logic [31:0] v);\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    v = cnt;\n"
      "  endtask\n"
      "  initial begin\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "  end\n"
      "endmodule\n",
      "result");

  EXPECT_EQ(val, 2u);
}

TEST(TaskDeclSim, DefaultTaskInAutomaticModuleIsAutomatic) {
  auto val = RunAndGet(
      "module automatic t;\n"
      "  logic [31:0] result;\n"
      "  task counter(output logic [31:0] v);\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    v = cnt;\n"
      "  endtask\n"
      "  initial begin\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "  end\n"
      "endmodule\n",
      "result");

  EXPECT_EQ(val, 1u);
}

TEST(TaskDeclSim, DefaultTaskInPackageIsStatic) {
  auto val = RunAndGet(
      "package pk;\n"
      "  task counter(output logic [31:0] v);\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    v = cnt;\n"
      "  endtask\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::*;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

TEST(TaskDeclSim, DefaultTaskInAutomaticPackageIsAutomatic) {
  auto val = RunAndGet(
      "package automatic pk;\n"
      "  task counter(output logic [31:0] v);\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    v = cnt;\n"
      "  endtask\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::*;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(TaskDeclSim, StaticVarInAutoTaskPersists) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task automatic counter(output logic [31:0] v);\n"
      "    static int cnt = 0;\n"
      "    cnt = cnt + 1;\n"
      "    v = cnt;\n"
      "  endtask\n"
      "  initial begin\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(TaskDeclSim, AutoVarInStaticTaskFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task static counter(output logic [31:0] v);\n"
      "    automatic int cnt = 0;\n"
      "    cnt = cnt + 1;\n"
      "    v = cnt;\n"
      "  endtask\n"
      "  initial begin\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "    counter(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(TaskDeclSim, ClassTaskIsAlwaysAutomatic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  task step(output int r);\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    r = cnt;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    obj.step(a);\n"
      "    obj.step(b);\n"
      "    obj.step(c);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 1u}, {"c", 1u}});
}

TEST(TaskDeclSim, SetupReturnsTaskItem) {
  SimFixture f;
  auto* task = f.arena.Create<ModuleItem>();
  task->kind = ModuleItemKind::kTaskDecl;
  task->name = "my_task";
  task->is_static = true;
  f.ctx.RegisterFunction("my_task", task);

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "my_task";

  auto* result = SetupTaskCall(call, f.ctx, f.arena);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->name, "my_task");

  TeardownTaskCall(result, call, f.ctx, f.arena);
}

}  // namespace
