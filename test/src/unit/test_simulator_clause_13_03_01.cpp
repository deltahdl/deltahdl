#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// §13.3.1: Static task variables persist between calls.
TEST(Sim13031, StaticTaskVarsPersist) {
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

// §13.3.1: Automatic task variables are fresh each call.
TEST(Sim13031, AutomaticTaskVarsFresh) {
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
  // cnt starts at 0 each call (automatic), so always 1.
  EXPECT_EQ(val, 1u);
}

// §13.3.1: Default task (no qualifier) in a module is static.
TEST(Sim13031, DefaultTaskIsStatic) {
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
  // Default is static: cnt persists, should be 2 after two calls.
  EXPECT_EQ(val, 2u);
}

// §13.3.1: Static task with input args still works.
TEST(Sim13031, StaticTaskWithInputArgs) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task static add_to(input logic [31:0] addend, output logic [31:0] v);\n"
      "    int acc;\n"
      "    acc = acc + addend;\n"
      "    v = acc;\n"
      "  endtask\n"
      "  initial begin\n"
      "    add_to(32'd10, result);\n"
      "    add_to(32'd20, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  // acc persists: 10 after first call, 30 after second.
  EXPECT_EQ(val, 30u);
}

// §13.3.1: SetupTaskCall returns null for function, not task.
TEST(Sim13031, SetupReturnsTaskItem) {
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

  TeardownTaskCall(result, call, f.ctx);
}

}  // namespace
