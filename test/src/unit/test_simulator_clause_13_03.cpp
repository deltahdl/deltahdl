#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(TaskCall, SetupReturnsTaskItem) {
  SimFixture f;

  auto* task = f.arena.Create<ModuleItem>();
  task->kind = ModuleItemKind::kTaskDecl;
  task->name = "my_task";
  f.ctx.RegisterFunction("my_task", task);

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "my_task";

  auto* result = SetupTaskCall(call, f.ctx, f.arena);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->name, "my_task");

  TeardownTaskCall(result, call, f.ctx);
}

TEST(TaskCall, SetupReturnsNullForFunction) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "my_func";
  f.ctx.RegisterFunction("my_func", func);

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "my_func";

  auto* result = SetupTaskCall(call, f.ctx, f.arena);
  EXPECT_EQ(result, nullptr);
}

TEST(TaskCall, SetupReturnsNullForUnknown) {
  SimFixture f;
  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "nonexistent";

  auto* result = SetupTaskCall(call, f.ctx, f.arena);
  EXPECT_EQ(result, nullptr);
}

TEST(Sim1303, TaskInputArg) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task set_val(input logic [31:0] v);\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    set_val(32'd99);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 99u);
}

TEST(Sim1303, TaskInoutArg) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task double_it(inout logic [31:0] v);\n"
      "    v = v * 2;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 32'd7;\n"
      "    double_it(x);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 14u);
}

TEST(Sim1303, TaskMultipleOutputArgs) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  task split(input logic [31:0] v, output logic [31:0] lo, hi);\n"
      "    lo = v & 32'hFFFF;\n"
      "    hi = (v >> 16) & 32'hFFFF;\n"
      "  endtask\n"
      "  initial begin\n"
      "    split(32'h0003_0007, a, b);\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 7u);
}

TEST(Sim1303, TaskCallsTask) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task inner(input logic [31:0] v);\n"
      "    x = v;\n"
      "  endtask\n"
      "  task outer;\n"
      "    inner(32'd42);\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    outer();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(Sim1303, TaskEmptyBody) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task nop;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 32'd1;\n"
      "    nop();\n"
      "    x = x + 32'd1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 2u);
}

}
