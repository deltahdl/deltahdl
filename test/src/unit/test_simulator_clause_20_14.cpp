// §20.14: Probabilistic distribution functions


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

TEST(SysTask, RandomReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$random", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, DistUniformReturns32Bit) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$dist_uniform",
                {MkInt(f.arena, 0), MkInt(f.arena, 0), MkInt(f.arena, 100)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_LE(result.ToUint64(), 100u);
}

TEST(SysTask, DistNormalReturns32Bit) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$dist_normal",
                {MkInt(f.arena, 0), MkInt(f.arena, 50), MkInt(f.arena, 10)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

}  // namespace
