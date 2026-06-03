#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PriorityIfViolationSim, PriorityIfSingleConditionNoMatchWarning) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("piw", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->qualifier = CaseQualifier::kPriority;
  stmt->condition = MakeInt(f.arena, 0);
  stmt->then_branch = MakeBlockAssign(f.arena, "piw", 30);

  RunStmt(stmt, f.ctx, f.arena);

  EXPECT_EQ(result_var->value.ToUint64(), 0u);

  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(PriorityIfViolationSim, PriorityIfChainWithElseAllFalseNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    priority if (0) x = 8'd1;\n"
      "    else if (0) x = 8'd2;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(PriorityIfViolationSim, PriorityIfChainNoMatchNoElseWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    priority if (0) x = 8'd1;\n"
      "    else if (0) x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(PriorityIfViolationSim, PriorityIfFirstConditionMatchNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    priority if (1) x = 8'd42;\n"
      "    else if (0) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(PriorityIfViolationSim, PriorityIfMultipleTrueNoOverlapWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    priority if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(PriorityIfViolationSim, PriorityIfChainMiddleBranchMatchNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    priority if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else if (a == 8'd2) x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §12.4.2.2: a violation check is allowed to sit inside a function or task. The
// check must still fire when the subroutine runs; here the unique-if conditions
// overlap on every call, so each invocation queues a uniqueness violation.
TEST(IfViolationMultiProcessSim, FunctionUniqueIfOverlapReportsViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  function bit chk(input bit a, input bit b);\n"
      "    unique if (a) chk = 1'b1;\n"
      "    else if (b) chk = 1'b0;\n"
      "  endfunction\n"
      "  initial r = chk(1'b1, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// A unique-if inside a function whose conditions are mutually exclusive on the
// call must not report; otherwise the per-subroutine check would be spurious.
TEST(IfViolationMultiProcessSim, FunctionUniqueIfSingleMatchNoViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  function bit chk(input bit a, input bit b);\n"
      "    unique if (a) chk = 1'b1;\n"
      "    else if (b) chk = 1'b0;\n"
      "  endfunction\n"
      "  initial r = chk(1'b1, 1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// A unique-if inside a function with no matching branch and no else reports the
// no-match violation, just as it would in a process body.
TEST(IfViolationMultiProcessSim, FunctionUniqueIfNoMatchNoElseReports) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  function bit chk(input bit a, input bit b);\n"
      "    unique if (a) chk = 1'b1;\n"
      "    else if (b) chk = 1'b0;\n"
      "  endfunction\n"
      "  initial r = chk(1'b0, 1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// A priority-if inside a function with no matching branch and no else likewise
// reports a violation from within the subroutine body.
TEST(IfViolationMultiProcessSim, FunctionPriorityIfNoMatchReports) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  function bit chk(input bit a, input bit b);\n"
      "    priority if (a) chk = 1'b1;\n"
      "    else if (b) chk = 1'b0;\n"
      "  endfunction\n"
      "  initial r = chk(1'b0, 1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §12.4.2.2: when two distinct processes both call the same function, the check
// runs once per caller and each execution is independent. Both callers pass
// overlapping arguments, so the shared function's uniqueness check fails in each
// calling process and the violation is reported twice.
TEST(IfViolationMultiProcessSim, TwoProcessesCallSharedFunctionReportTwice) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r1, r2;\n"
      "  function bit chk(input bit a, input bit b);\n"
      "    unique if (a) chk = 1'b1;\n"
      "    else if (b) chk = 1'b0;\n"
      "  endfunction\n"
      "  initial r1 = chk(1'b1, 1'b1);\n"
      "  initial r2 = chk(1'b1, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 2u);
}

// §12.4.2.2: the per-caller executions are independent, so a failure in one
// calling process does not implicate another. Here the first caller passes
// overlapping arguments (violation) while the second passes mutually exclusive
// arguments (no violation); exactly one report is produced.
TEST(IfViolationMultiProcessSim, SharedFunctionOneCallerViolatesOtherPasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r1, r2;\n"
      "  function bit chk(input bit a, input bit b);\n"
      "    unique if (a) chk = 1'b1;\n"
      "    else if (b) chk = 1'b0;\n"
      "  endfunction\n"
      "  initial r1 = chk(1'b1, 1'b1);\n"
      "  initial r2 = chk(1'b1, 1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

// §12.4.2.2: a violation queued by a function check belongs to the calling
// process, so when that process (an always_comb) is re-triggered and its final
// re-evaluation passes, the stale report is flushed. The first evaluation calls
// chk(1,1) (overlap, violation queued in the always_comb process); the
// nonblocking update of b re-triggers the procedure, and chk(1,0) on resume no
// longer overlaps, so the pending violation is flushed before it can mature.
TEST(IfViolationMultiProcessSim, AlwaysCombRetriggerFlushesFunctionViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  function bit chk(input bit x, input bit y);\n"
      "    unique if (x) chk = 1'b1;\n"
      "    else if (y) chk = 1'b0;\n"
      "  endfunction\n"
      "  always_comb z = chk(a, b);\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §12.4.2.2 names a "task or function": the rule covers checks in either kind of
// subroutine. A task body runs through the statement-execution path, so a
// unique-if with overlapping conditions inside a task must still queue a
// violation against the calling process.
TEST(IfViolationMultiProcessSim, TaskUniqueIfOverlapReportsViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  task chk(input bit a, input bit b);\n"
      "    unique if (a) r = 8'd1;\n"
      "    else if (b) r = 8'd0;\n"
      "  endtask\n"
      "  initial begin chk(1'b1, 1'b1); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// A clean (mutually exclusive) unique-if inside a task must not report, so the
// task-body check is not spuriously firing.
TEST(IfViolationMultiProcessSim, TaskUniqueIfSingleMatchNoViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  task chk(input bit a, input bit b);\n"
      "    unique if (a) r = 8'd1;\n"
      "    else if (b) r = 8'd0;\n"
      "  endtask\n"
      "  initial begin chk(1'b1, 1'b0); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §12.4.2.2: when two distinct processes call the same task, the check runs once
// per caller and each execution is independent, so an overlap that fails in both
// callers is reported twice.
TEST(IfViolationMultiProcessSim, TwoProcessesCallSharedTaskReportTwice) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  task chk(input bit a, input bit b);\n"
      "    unique if (a) r = 8'd1;\n"
      "    else if (b) r = 8'd0;\n"
      "  endtask\n"
      "  initial begin chk(1'b1, 1'b1); end\n"
      "  initial begin chk(1'b1, 1'b1); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 2u);
}

}
