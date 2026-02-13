#include <gtest/gtest.h>

#include <cstring>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// ============================================================================
// Test helpers (shared with test_systask.cpp)
// ============================================================================

struct SysTaskMathFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static double ResultToDouble(const Logic4Vec& vec) {
  uint64_t bits = vec.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

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

// ============================================================================
// Math functions (section 20.8)
// ============================================================================

TEST(SysTaskMath, LnOfE) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$ln", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTaskMath, Log10Of100) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$log10", {MkInt(f.arena, 100)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 2.0);
}

TEST(SysTaskMath, ExpOf0) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$exp", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1.0);
}

TEST(SysTaskMath, SqrtOf16) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$sqrt", {MkInt(f.arena, 16)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 4.0);
}

TEST(SysTaskMath, SqrtOf9) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$sqrt", {MkInt(f.arena, 9)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 3.0);
}

TEST(SysTaskMath, PowOf2And10) {
  SysTaskMathFixture f;
  auto* expr =
      MkSysCall(f.arena, "$pow", {MkInt(f.arena, 2), MkInt(f.arena, 10)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1024.0);
}

TEST(SysTaskMath, FloorOf7) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$floor", {MkInt(f.arena, 7)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 7.0);
}

TEST(SysTaskMath, CeilOf7) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$ceil", {MkInt(f.arena, 7)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 7.0);
}

TEST(SysTaskMath, SinOf0) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$sin", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTaskMath, CosOf0) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$cos", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1.0);
}

TEST(SysTaskMath, TanOf0) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$tan", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTaskMath, Atan2Of0And1) {
  SysTaskMathFixture f;
  auto* expr =
      MkSysCall(f.arena, "$atan2", {MkInt(f.arena, 0), MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTaskMath, HypotOf3And4) {
  SysTaskMathFixture f;
  auto* expr =
      MkSysCall(f.arena, "$hypot", {MkInt(f.arena, 3), MkInt(f.arena, 4)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 5.0);
}

TEST(SysTaskMath, SinhOf0) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$sinh", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTaskMath, CoshOf0) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$cosh", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1.0);
}

TEST(SysTaskMath, AsinOf0) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$asin", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTaskMath, AcosOf1) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$acos", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTaskMath, AtanOf0) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$atan", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}
