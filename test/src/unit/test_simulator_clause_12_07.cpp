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

TEST(StmtExec, ForeachIteratesOverArrayWidth) {
  StmtFixture f;

  auto* arr = f.ctx.CreateVariable("arr", 4);
  arr->value = MakeLogic4VecVal(f.arena, 4, 0);

  auto* sum = f.ctx.CreateVariable("sum", 32);
  sum->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* sum_id = MakeId(f.arena, "sum");
  auto* one = MakeInt(f.arena, 1);
  auto* add_expr = f.arena.Create<Expr>();
  add_expr->kind = ExprKind::kBinary;
  add_expr->op = TokenKind::kPlus;
  add_expr->lhs = sum_id;
  add_expr->rhs = one;

  auto* body = f.arena.Create<Stmt>();
  body->kind = StmtKind::kBlockingAssign;
  body->lhs = MakeId(f.arena, "sum");
  body->rhs = add_expr;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeId(f.arena, "arr");
  stmt->foreach_vars.push_back("i");
  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(sum->value.ToUint64(), 4u);
}

TEST(StmtExec, ForeachEmptyArrayNoOp) {
  StmtFixture f;

  auto* arr = f.ctx.CreateVariable("empty", 0);
  (void)arr;
  auto* sum = f.ctx.CreateVariable("count", 32);
  sum->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* body = MakeBlockAssign(f.arena, "count", 1);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeId(f.arena, "empty");
  stmt->foreach_vars.push_back("i");
  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(sum->value.ToUint64(), 0u);
}

TEST(StmtExec, ForeachNoVarsStillIterates) {
  StmtFixture f;
  auto* arr = f.ctx.CreateVariable("arr2", 3);
  arr->value = MakeLogic4VecVal(f.arena, 3, 0);

  auto* cnt = f.ctx.CreateVariable("cnt", 32);
  cnt->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = MakeId(f.arena, "cnt");
  add->rhs = MakeInt(f.arena, 1);

  auto* body = f.arena.Create<Stmt>();
  body->kind = StmtKind::kBlockingAssign;
  body->lhs = MakeId(f.arena, "cnt");
  body->rhs = add;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeId(f.arena, "arr2");

  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(cnt->value.ToUint64(), 3u);
}

TEST(StmtExec, ForeachBreakExitsLoop) {
  StmtFixture f;
  auto* arr = f.ctx.CreateVariable("brk_arr", 10);
  arr->value = MakeLogic4VecVal(f.arena, 10, 0);

  auto* cnt = f.ctx.CreateVariable("brk_cnt", 32);
  cnt->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = MakeId(f.arena, "brk_cnt");
  add->rhs = MakeInt(f.arena, 1);

  auto* inc_stmt = f.arena.Create<Stmt>();
  inc_stmt->kind = StmtKind::kBlockingAssign;
  inc_stmt->lhs = MakeId(f.arena, "brk_cnt");
  inc_stmt->rhs = add;

  auto* break_stmt = f.arena.Create<Stmt>();
  break_stmt->kind = StmtKind::kBreak;

  auto* cmp = f.arena.Create<Expr>();
  cmp->kind = ExprKind::kBinary;
  cmp->op = TokenKind::kEqEq;
  cmp->lhs = MakeId(f.arena, "brk_cnt");
  cmp->rhs = MakeInt(f.arena, 3);

  auto* if_stmt = f.arena.Create<Stmt>();
  if_stmt->kind = StmtKind::kIf;
  if_stmt->condition = cmp;
  if_stmt->then_branch = break_stmt;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(inc_stmt);
  block->stmts.push_back(if_stmt);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeId(f.arena, "brk_arr");
  stmt->foreach_vars.push_back("i");
  stmt->body = block;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(cnt->value.ToUint64(), 3u);
}

TEST(StmtExec, ForeachIteratorVariableAccessible) {
  StmtFixture f;
  auto* arr = f.ctx.CreateVariable("itarr", 5);
  arr->value = MakeLogic4VecVal(f.arena, 5, 0);

  auto* last = f.ctx.CreateVariable("last_i", 32);
  last->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* body = f.arena.Create<Stmt>();
  body->kind = StmtKind::kBlockingAssign;
  body->lhs = MakeId(f.arena, "last_i");
  body->rhs = MakeId(f.arena, "i");

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeId(f.arena, "itarr");
  stmt->foreach_vars.push_back("i");
  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);

  EXPECT_EQ(last->value.ToUint64(), 4u);
}

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
