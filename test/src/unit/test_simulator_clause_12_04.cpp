// §12.4: Conditional if–else statement

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/compiled_sim.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>

using namespace delta;

struct CompiledSimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};
namespace {

TEST(CompiledSim, ExecuteIfElse) {
  CompiledSimFixture f;
  auto *sel = f.ctx.CreateVariable("sel", 1);
  sel->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto *out = f.ctx.CreateVariable("out", 32);
  out->value = MakeLogic4VecVal(f.arena, 32, 0);

  // AST: if (sel) out = 1; else out = 0;
  auto *cond = f.arena.Create<Expr>();
  cond->kind = ExprKind::kIdentifier;
  cond->text = "sel";

  auto *then_lhs = f.arena.Create<Expr>();
  then_lhs->kind = ExprKind::kIdentifier;
  then_lhs->text = "out";
  auto *one = f.arena.Create<Expr>();
  one->kind = ExprKind::kIntegerLiteral;
  one->int_val = 1;
  auto *then_stmt = f.arena.Create<Stmt>();
  then_stmt->kind = StmtKind::kBlockingAssign;
  then_stmt->lhs = then_lhs;
  then_stmt->rhs = one;

  auto *else_lhs = f.arena.Create<Expr>();
  else_lhs->kind = ExprKind::kIdentifier;
  else_lhs->text = "out";
  auto *zero = f.arena.Create<Expr>();
  zero->kind = ExprKind::kIntegerLiteral;
  zero->int_val = 0;
  auto *else_stmt = f.arena.Create<Stmt>();
  else_stmt->kind = StmtKind::kBlockingAssign;
  else_stmt->lhs = else_lhs;
  else_stmt->rhs = zero;

  auto *if_stmt = f.arena.Create<Stmt>();
  if_stmt->kind = StmtKind::kIf;
  if_stmt->condition = cond;
  if_stmt->then_branch = then_stmt;
  if_stmt->else_branch = else_stmt;

  auto *block = f.arena.Create<Stmt>();
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

} // namespace
