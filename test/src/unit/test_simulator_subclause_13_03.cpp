#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
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

  TeardownTaskCall(result, call, f.ctx, f.arena);
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

TEST(TaskSim, TaskCallsTask) {
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

TEST(TaskSim, TaskEmptyBody) {
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

TEST(TaskSim, TaskReturnEarlyExit) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task maybe_set(input logic [31:0] v);\n"
      "    if (v == 0) return;\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 32'd1;\n"
      "    maybe_set(32'd0);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 1u);
}

TEST(TaskSim, StaticTaskArgsRetainValues) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task static bump(inout logic [31:0] v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    result = 32'd0;\n"
      "    bump(result);\n"
      "    bump(result);\n"
      "    bump(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(TaskSim, AutomaticTaskInputFromCaller) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task automatic compute(input logic [31:0] a, input logic [31:0] b,\n"
      "                         output logic [31:0] out);\n"
      "    out = a + b;\n"
      "  endtask\n"
      "  initial begin\n"
      "    compute(32'd15, 32'd27, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 42u);
}

TEST(TaskSim, FormalArgInheritedTypeRoundTripsFullWidth) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] result_a;\n"
      "  logic [7:0] result_b;\n"
      "  task fill(output logic [7:0] a, b);\n"
      "    a = 8'hA5;\n"
      "    b = 8'h5A;\n"
      "  endtask\n"
      "  initial fill(result_a, result_b);\n"
      "endmodule\n",
      "result_b");
  EXPECT_EQ(val, 0x5Au);
}

// §13.2 and §13.3 (printed page 335): a task may contain time-controlling
// statements, and control returns to the enabling process only when the task
// has completed, so the time of the return may differ from the time of the
// call; §8.6 (printed page 183) has an object's task enabled through its
// handle, `d.run();`, as any of its methods is. A class task's delay was run
// without consuming time, the call going to the function interpreter, so the
// read of $time after it gave 0 rather than 50.
TEST(TaskSim, ClassTaskCalledThroughAHandleConsumesItsDelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class drv;\n"
      "    task run();\n"
      "      #50;\n"
      "      x = $time;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv d = new;\n"
      "    x = 0;\n"
      "    d.run();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 50u);
}

// §13.3: control comes back to the enabling process after the task's delay,
// so the statement after the call runs at the time the task ended.
TEST(TaskSim, ClassTaskCalledThroughAHandleReturnsAfterItsDelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] y;\n"
      "  class drv;\n"
      "    task run();\n"
      "      #70;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv d = new;\n"
      "    d.run();\n"
      "    y = $time;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 70u);
}

// §13.3 with §9.4.2: an event control inside the class task suspends the
// enabling process until the edge, here the posedge another process drives
// at time 30.
TEST(TaskSim, ClassTaskCalledThroughAHandleWaitsForAnEdge) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  logic clk;\n"
      "  class drv;\n"
      "    task run();\n"
      "      @(posedge clk);\n"
      "      x = $time;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv d = new;\n"
      "    x = 0;\n"
      "    d.run();\n"
      "  end\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #30 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 30u);
}

// §13.3: a class task's input argument binds for the body, and a property of
// the object the handle refers to is written by it (§8.6), after the delay.
TEST(TaskSim, ClassTaskCalledThroughAHandleBindsItsArgumentAndThis) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class drv;\n"
      "    int count;\n"
      "    task run(input int n);\n"
      "      #10;\n"
      "      count = n + 1;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv d = new;\n"
      "    x = 0;\n"
      "    d.run(41);\n"
      "    x = d.count;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

// §13.3 with §8.11: two activations of one class task on two objects, each
// suspended on its delay while the other runs, each write their own object's
// property when they resume -- the object a task runs on travels with the
// process, parked while it is suspended as its locals are, so the activation
// resuming first does not write through the other's `this`.
TEST(TaskSim, TwoSuspendedClassTasksEachWriteTheirOwnObject) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class drv;\n"
      "    int id, count;\n"
      "    task run();\n"
      "      #(10 * id);\n"
      "      count = id * 100 + $time;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv a = new;\n"
      "    drv b = new;\n"
      "    a.id = 1;\n"
      "    b.id = 2;\n"
      "    fork\n"
      "      a.run();\n"
      "      b.run();\n"
      "    join\n"
      "    x = a.count * 1000 + b.count;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 110220u);
}

// §13.3 (printed page 335): a task enabled as a statement runs to completion,
// its timing controls consuming time, before the enabling process goes on;
// §26.3 (printed page 808) references a package's declaration through the
// package scope resolution operator. A package task enabled as `p::pause(9)`
// was dropped whole, so the time read after it was the 6 of the imported
// enable alone rather than 15.
TEST(TaskSim, PackageTaskEnabledThroughItsScopedNameConsumesItsDelay) {
  auto val = RunAndGet(
      "package p;\n"
      "  task pause(int d);\n"
      "    #d;\n"
      "  endtask\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    pause(6);\n"
      "    p::pause(9);\n"
      "    x = $time;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 15u);
}

}  // namespace
