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

TEST(StmtExec, ForeachContinueSkipsIteration) {
  StmtFixture f;
  auto* arr = f.ctx.CreateVariable("carr", 4);
  arr->value = MakeLogic4VecVal(f.arena, 4, 0);

  auto* cnt = f.ctx.CreateVariable("ccnt", 32);
  cnt->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = MakeId(f.arena, "ccnt");
  add->rhs = MakeInt(f.arena, 1);

  auto* inc_stmt = f.arena.Create<Stmt>();
  inc_stmt->kind = StmtKind::kBlockingAssign;
  inc_stmt->lhs = MakeId(f.arena, "ccnt");
  inc_stmt->rhs = add;

  auto* cont_stmt = f.arena.Create<Stmt>();
  cont_stmt->kind = StmtKind::kContinue;

  auto* cmp = f.arena.Create<Expr>();
  cmp->kind = ExprKind::kBinary;
  cmp->op = TokenKind::kEqEq;
  cmp->lhs = MakeId(f.arena, "i");
  cmp->rhs = MakeInt(f.arena, 1);

  auto* if_stmt = f.arena.Create<Stmt>();
  if_stmt->kind = StmtKind::kIf;
  if_stmt->condition = cmp;
  if_stmt->then_branch = cont_stmt;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(if_stmt);
  block->stmts.push_back(inc_stmt);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeId(f.arena, "carr");
  stmt->foreach_vars.push_back("i");
  stmt->body = block;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(cnt->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachBasic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    arr[0] = 8'd1;\n"
      "    arr[1] = 8'd2;\n"
      "    arr[2] = 8'd3;\n"
      "    arr[3] = 8'd4;\n"
      "    total = 8'd0;\n"
      "    foreach (arr[i]) total = total + arr[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LoopStatementSim, ForeachBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [3];\n"
      "  logic [7:0] sum, cnt;\n"
      "  initial begin\n"
      "    arr[0] = 8'd10;\n"
      "    arr[1] = 8'd20;\n"
      "    arr[2] = 8'd30;\n"
      "    sum = 8'd0;\n"
      "    cnt = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      sum = sum + arr[i];\n"
      "      cnt = cnt + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vs = f.ctx.FindVariable("sum");
  auto* vc = f.ctx.FindVariable("cnt");
  ASSERT_NE(vs, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(vs->value.ToUint64(), 60u);
  EXPECT_EQ(vc->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [5];\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = 8'd0;\n"
      "    cnt = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      cnt = cnt + 8'd1;\n"
      "      if (cnt == 8'd3) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachIteratorValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] last_i;\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = 8'd0;\n"
      "    last_i = 8'd0;\n"
      "    foreach (arr[i]) last_i = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("last_i");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] sum;\n"
      "  initial begin\n"
      "    arr[0] = 8'd1;\n"
      "    arr[1] = 8'd2;\n"
      "    arr[2] = 8'd3;\n"
      "    arr[3] = 8'd4;\n"
      "    sum = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      if (i[7:0] == 8'd1) continue;\n"
      "      sum = sum + arr[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(LoopStatementSim, ForeachWriteArrayElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [3];\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = i[7:0] + 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a0 = f.ctx.FindVariable("arr[0]");
  auto* a1 = f.ctx.FindVariable("arr[1]");
  auto* a2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(a0, nullptr);
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(a0->value.ToUint64(), 10u);
  EXPECT_EQ(a1->value.ToUint64(), 11u);
  EXPECT_EQ(a2->value.ToUint64(), 12u);
}

}  // namespace
