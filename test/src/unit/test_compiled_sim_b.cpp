// Non-LRM tests

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/compiled_sim.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

TEST(CompiledSim, NullBodyNotCompilable) {
  EXPECT_FALSE(ProcessCompiler::IsCompilable(nullptr));
}

TEST(CompiledSim, CompileReturnsValidForCombinational) {
  Arena arena;
  auto* assign = arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;

  auto* block = arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(42, block);
  EXPECT_TRUE(compiled.IsValid());
  EXPECT_EQ(compiled.Id(), 42u);
}

TEST(CompiledSim, ExecuteBlockingAssign) {
  CompiledSimFixture f;
  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Build AST: x = 42
  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "x";
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kIntegerLiteral;
  rhs->int_val = 42;
  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = rhs;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(1, block);
  EXPECT_TRUE(compiled.IsValid());
  compiled.Execute(f.ctx);
  EXPECT_EQ(x_var->value.ToUint64(), 42u);
}

TEST(CompiledSim, ExecuteExpressionEval) {
  CompiledSimFixture f;
  auto* a_var = f.ctx.CreateVariable("a", 32);
  a_var->value = MakeLogic4VecVal(f.arena, 32, 10);
  auto* b_var = f.ctx.CreateVariable("b", 32);
  b_var->value = MakeLogic4VecVal(f.arena, 32, 20);
  auto* c_var = f.ctx.CreateVariable("c", 32);
  c_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // AST: c = a + b
  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "c";
  auto* a_ref = f.arena.Create<Expr>();
  a_ref->kind = ExprKind::kIdentifier;
  a_ref->text = "a";
  auto* b_ref = f.arena.Create<Expr>();
  b_ref->kind = ExprKind::kIdentifier;
  b_ref->text = "b";
  auto* add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = a_ref;
  add->rhs = b_ref;
  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = add;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(1, block);
  compiled.Execute(f.ctx);
  EXPECT_EQ(c_var->value.ToUint64(), 30u);
}

TEST(CompiledSim, ExecuteIfElse) {
  CompiledSimFixture f;
  auto* sel = f.ctx.CreateVariable("sel", 1);
  sel->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* out = f.ctx.CreateVariable("out", 32);
  out->value = MakeLogic4VecVal(f.arena, 32, 0);

  // AST: if (sel) out = 1; else out = 0;
  auto* cond = f.arena.Create<Expr>();
  cond->kind = ExprKind::kIdentifier;
  cond->text = "sel";

  auto* then_lhs = f.arena.Create<Expr>();
  then_lhs->kind = ExprKind::kIdentifier;
  then_lhs->text = "out";
  auto* one = f.arena.Create<Expr>();
  one->kind = ExprKind::kIntegerLiteral;
  one->int_val = 1;
  auto* then_stmt = f.arena.Create<Stmt>();
  then_stmt->kind = StmtKind::kBlockingAssign;
  then_stmt->lhs = then_lhs;
  then_stmt->rhs = one;

  auto* else_lhs = f.arena.Create<Expr>();
  else_lhs->kind = ExprKind::kIdentifier;
  else_lhs->text = "out";
  auto* zero = f.arena.Create<Expr>();
  zero->kind = ExprKind::kIntegerLiteral;
  zero->int_val = 0;
  auto* else_stmt = f.arena.Create<Stmt>();
  else_stmt->kind = StmtKind::kBlockingAssign;
  else_stmt->lhs = else_lhs;
  else_stmt->rhs = zero;

  auto* if_stmt = f.arena.Create<Stmt>();
  if_stmt->kind = StmtKind::kIf;
  if_stmt->condition = cond;
  if_stmt->then_branch = then_stmt;
  if_stmt->else_branch = else_stmt;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(if_stmt);

  auto compiled = ProcessCompiler::Compile(1, block);
  compiled.Execute(f.ctx);
  EXPECT_EQ(out->value.ToUint64(), 1u);

  // Change sel to 0, re-execute.
  sel->value = MakeLogic4VecVal(f.arena, 1, 0);
  compiled.Execute(f.ctx);
  EXPECT_EQ(out->value.ToUint64(), 0u);
}

}  // namespace
