// §18.13: Random number system functions and methods


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

TEST(SysTask, UrandomReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, UrandomRangeInBounds) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range",
                         {MkInt(f.arena, 10), MkInt(f.arena, 5)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  uint64_t val = result.ToUint64();
  EXPECT_GE(val, 5u);
  EXPECT_LE(val, 10u);
}

}  // namespace
