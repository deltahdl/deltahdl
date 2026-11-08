#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast_stmt.h"
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    priority if (0) x = 8'd1;\n"
      "    else if (0) x = 8'd2;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(PriorityIfViolationSim, PriorityIfChainNoMatchNoElseWarning) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    priority if (0) x = 8'd1;\n"
      "    else if (0) x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(PriorityIfViolationSim, PriorityIfFirstConditionMatchNoWarning) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    priority if (1) x = 8'd42;\n"
      "    else if (0) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(PriorityIfViolationSim, PriorityIfMultipleTrueNoOverlapWarning) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    priority if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(PriorityIfViolationSim, PriorityIfChainMiddleBranchMatchNoWarning) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    priority if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else if (a == 8'd2) x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

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

TEST(IfViolationMultiProcessSim,
     TwoProcessesCallSharedUnique0FunctionReportTwice) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r1, r2;\n"
      "  function bit chk(input bit a, input bit b);\n"
      "    unique0 if (a) chk = 1'b1;\n"
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

TEST(IfViolationMultiProcessSim,
     TwoProcessesCallSharedPriorityFunctionReportTwice) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r1, r2;\n"
      "  function bit chk(input bit a, input bit b);\n"
      "    priority if (a) chk = 1'b1;\n"
      "    else if (b) chk = 1'b0;\n"
      "  endfunction\n"
      "  initial r1 = chk(1'b0, 1'b0);\n"
      "  initial r2 = chk(1'b0, 1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 2u);
}

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

}  // namespace
