// §20.15: Stochastic analysis tasks and functions


#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

static Expr* MkSysCall(Arena& arena, std::string_view name,
                       std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

static Expr* MkInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

namespace {

TEST(SysTask, QInitializeReturnsZero) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$q_initialize",
                {MkInt(f.arena, 1), MkInt(f.arena, 1), MkInt(f.arena, 100)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, QFullReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$q_full", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
