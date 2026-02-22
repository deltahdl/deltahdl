// §11.4.1: Assignment operators

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

TEST(CompiledSim, ExecuteExpressionEval) {
  CompiledSimFixture f;
  auto *a_var = f.ctx.CreateVariable("a", 32);
  a_var->value = MakeLogic4VecVal(f.arena, 32, 10);
  auto *b_var = f.ctx.CreateVariable("b", 32);
  b_var->value = MakeLogic4VecVal(f.arena, 32, 20);
  auto *c_var = f.ctx.CreateVariable("c", 32);
  c_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // AST: c = a + b
  auto *lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "c";
  auto *a_ref = f.arena.Create<Expr>();
  a_ref->kind = ExprKind::kIdentifier;
  a_ref->text = "a";
  auto *b_ref = f.arena.Create<Expr>();
  b_ref->kind = ExprKind::kIdentifier;
  b_ref->text = "b";
  auto *add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = a_ref;
  add->rhs = b_ref;
  auto *assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = add;

  auto *block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(1, block);
  compiled.Execute(f.ctx);
  EXPECT_EQ(c_var->value.ToUint64(), 30u);
}

} // namespace
