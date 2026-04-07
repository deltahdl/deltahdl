#include <cstdint>
#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, MixedRepeatInsideFor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      repeat (2) x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(StmtExec, RandcaseSelectsBranch) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("r", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 1), MakeBlockAssign(f.arena, "r", 10)});
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 1), MakeBlockAssign(f.arena, "r", 20)});

  RunStmt(stmt, f.ctx, f.arena);
  uint64_t val = result_var->value.ToUint64();
  EXPECT_TRUE(val == 10 || val == 20);
}

TEST(StmtExec, RandcaseAllZeroWeightsNoOp) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 0), MakeBlockAssign(f.arena, "rz", 10)});
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 0), MakeBlockAssign(f.arena, "rz", 20)});

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(StmtExec, RandcaseSingleBranchAlwaysSelected) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rs", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 5), MakeBlockAssign(f.arena, "rs", 42)});

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(StmtExec, RandcaseRespectsWeights) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rw", 32);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 100), MakeBlockAssign(f.arena, "rw", 1)});
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 0), MakeBlockAssign(f.arena, "rw", 2)});

  for (int i = 0; i < 10; ++i) {
    result_var->value = MakeLogic4VecVal(f.arena, 32, 0);
    RunStmt(stmt, f.ctx, f.arena);
    EXPECT_EQ(result_var->value.ToUint64(), 1u);
  }
}

TEST(StmtExec, RandcaseSelectsItem) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rc", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 1), MakeBlockAssign(f.arena, "rc", 10)});
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 1), MakeBlockAssign(f.arena, "rc", 20)});
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 1), MakeBlockAssign(f.arena, "rc", 30)});

  RunStmt(stmt, f.ctx, f.arena);
  uint64_t val = result_var->value.ToUint64();
  EXPECT_TRUE(val == 10 || val == 20 || val == 30);
}

TEST(RandcaseStatementSim, RandcaseExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randcase\n"
      "      1: x = 8'd10;\n"
      "      1: x = 8'd20;\n"
      "      1: x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint64_t val = var->value.ToUint64();
  EXPECT_TRUE(val == 10 || val == 20 || val == 30);
}

TEST(RandcaseStatementSim, RandcaseZeroWeightsNoAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd99;\n"
      "    randcase\n"
      "      0: x = 8'd10;\n"
      "      0: x = 8'd20;\n"
      "    endcase\n"
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
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(RandcaseStatementSim, RandcaseVaryingWeights) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randcase\n"
      "      10: x = 8'd1;\n"
      "      30: x = 8'd2;\n"
      "      60: x = 8'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint64_t val = var->value.ToUint64();
  EXPECT_TRUE(val == 1 || val == 2 || val == 3);
}

TEST(RandcaseStatementSim, RandcaseBlockBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    y = 8'd0;\n"
      "    randcase\n"
      "      1: begin x = 8'd1; y = 8'd2; end\n"
      "      1: begin x = 8'd3; y = 8'd4; end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  uint64_t xv = x->value.ToUint64();
  uint64_t yv = y->value.ToUint64();
  EXPECT_TRUE((xv == 1 && yv == 2) || (xv == 3 && yv == 4));
}

TEST(RandcaseStatementSim, RandcaseSingleBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randcase\n"
      "      1: x = 8'd42;\n"
      "    endcase\n"
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
}

}  // namespace
