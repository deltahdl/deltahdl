// §20.12: Sampled value system functions


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

TEST(SysTask, SampledReturnsInput) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$sampled", {MkInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(SysTask, RoseReturnsZeroOrOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$rose", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_LE(result.ToUint64(), 1u);
}

TEST(SysTask, FellReturnsZeroOrOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$fell", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_LE(result.ToUint64(), 1u);
}

TEST(SysTask, StableReturnsZeroOrOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stable", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_LE(result.ToUint64(), 1u);
}

TEST(SysTask, PastReturnsValue) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$past", {MkInt(f.arena, 7)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, ChangedReturnsZeroOrOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$changed", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_LE(result.ToUint64(), 1u);
}

}  // namespace
