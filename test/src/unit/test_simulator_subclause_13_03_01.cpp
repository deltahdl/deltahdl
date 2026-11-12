#include <gtest/gtest.h>

#include <string>

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

constexpr const char* kCountingTask =
    "(output int r); int c; c++; r = c; endtask\n";

std::string CountingTask(const char* head) {
  return std::string("  ") + head + kCountingTask;
}

TEST(TaskLifetimeSim, AnInterfaceTaskIsStaticUnlessTheInterfaceIsAutomatic) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface i;\n" + CountingTask("task t") +
                     "endinterface\n"
                     "interface automatic ia;\n" +
                     CountingTask("task ta") + CountingTask("task static ts") +
                     "endinterface\n"
                     "module m;\n"
                     "  i u(); ia v();\n"
                     "  int a, b, c, d, e, g;\n"
                     "  initial begin\n"
                     "    u.t(a); u.t(b); v.ta(c); v.ta(d); v.ts(e); v.ts(g);\n"
                     "    $display(\"%0d %0d %0d %0d %0d %0d\", a, b, c, d, e, "
                     "g);\n"
                     "  end\n"
                     "endmodule\n",
                 f),
      "1 2 1 1 1 2\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(TaskLifetimeSim, AProgramTaskIsStaticUnlessTheProgramIsAutomatic) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program p;\n" + CountingTask("task t") +
                     "  int a, b;\n"
                     "  initial begin\n"
                     "    #1 t(a); t(b);\n"
                     "    $display(\"%0d %0d\", a, b);\n"
                     "  end\n"
                     "endprogram\n"
                     "program automatic q;\n" +
                     CountingTask("task ta") + CountingTask("task static ts") +
                     "  int a, b, e, g;\n"
                     "  initial begin\n"
                     "    #2 ta(a); ta(b); ts(e); ts(g);\n"
                     "    $display(\"%0d %0d %0d %0d\", a, b, e, g);\n"
                     "  end\n"
                     "endprogram\n",
                 f),
      "1 2\n1 1 1 2\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

std::string CountingTaskCaller(const char* kind, const char* name,
                               const char* task, int delay) {
  std::string d = std::to_string(delay);
  return std::string(kind) + " " + name + ";\n" + CountingTask(task) +
         "  int x, y;\n  initial begin #" + d + " t(x); t(y); $display(\"" +
         name + " %0d %0d\", x, y); end\nend" +
         (std::string(kind).find("module") != std::string::npos ? "module"
          : std::string(kind).find("interface") != std::string::npos
              ? "interface"
              : "program") +
         "\n";
}

TEST(TaskLifetimeSim,
     DISABLED_ATaskKeepsItsOwnLifetimeBesideASameNamedTaskElsewhere) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops(
          CountingTaskCaller("module", "sa", "task t", 1) +
              CountingTaskCaller("module", "aa", "task automatic t", 2) +
              CountingTaskCaller("module automatic", "ma", "task t", 3) +
              CountingTaskCaller("interface automatic", "ia", "task t", 4) +
              CountingTaskCaller("program automatic", "pa", "task t", 5) +
              CountingTaskCaller("module", "sb", "task t", 6) +
              CountingTaskCaller("program", "ps", "task t", 7) +
              "module top; sa a(); aa b(); ma c(); ia d(); sb e(); "
              "endmodule\n",
          f),
      "sa 1 2\naa 1 1\nma 1 1\nia 1 1\npa 1 1\nsb 1 2\nps 1 2\n");
}

TEST(TaskLifetimeSim,
     AnAutomaticTaskEnabledByAHierarchicalNameGetsItsOwnItemsPerCall) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops("module c;\n"
                              "  task automatic t(input int d, output int r);\n"
                              "    int k;\n"
                              "    k++;\n"
                              "    #d r = k * 10 + d;\n"
                              "  endtask\n"
                              "endmodule\n"
                              "module top;\n"
                              "  c u1();\n"
                              "  int a, b;\n"
                              "  initial fork u1.t(3, a); u1.t(5, b); join\n"
                              "  initial #9 $display(\"%0d %0d\", a, b);\n"
                              "endmodule\n",
                              f),
            "13 15\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
