#include <cmath>
#include <cstring>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

// Builds a real-valued literal so the §20.8.2 functions can be exercised with
// the real arguments the LRM says they accept (no shared builder exists yet).
static Expr* MkReal(Arena& arena, double v) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kRealLiteral;
  e->real_val = v;
  return e;
}

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

// §20.8.2 (C2/C3): the remaining Table 20-4 entries must produce the same value
// as their C-library counterpart. Comparing against the std function with a
// real argument also exercises real-argument acceptance from C1.
TEST(SysTaskMath, TanhMatchesCLibrary) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$tanh", {MkReal(f.arena, 0.5)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), std::tanh(0.5));
}

TEST(SysTaskMath, AsinhMatchesCLibrary) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$asinh", {MkReal(f.arena, 0.5)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), std::asinh(0.5));
}

TEST(SysTaskMath, AcoshMatchesCLibrary) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$acosh", {MkReal(f.arena, 2.0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), std::acosh(2.0));
}

TEST(SysTaskMath, AtanhMatchesCLibrary) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$atanh", {MkReal(f.arena, 0.5)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), std::atanh(0.5));
}

// §20.8.2 (C1): these functions return a real result type, so the evaluated
// value is flagged as real rather than a plain bit vector.
TEST(SysTaskMath, ReturnsRealResultType) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$sqrt", {MkInt(f.arena, 16)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
}

// §20.8.2 (C1): a real-valued argument is accepted and carried through the
// computation ($sqrt(2.25) == 1.5).
TEST(SysTaskMath, AcceptsRealArgument) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$sqrt", {MkReal(f.arena, 2.25)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1.5);
}

// §20.8.2 (C2): out-of-domain inputs must follow C-library behavior. A negative
// argument to $sqrt yields NaN, exactly as std::sqrt does.
TEST(SysTaskMath, SqrtOfNegativeIsNaN) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$sqrt", {MkReal(f.arena, -1.0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(std::isnan(ResultToDouble(result)));
}

// §20.8.2 (C2): $acos outside [-1, 1] returns NaN, matching std::acos.
TEST(SysTaskMath, AcosOutOfDomainIsNaN) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$acos", {MkReal(f.arena, 2.0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(std::isnan(ResultToDouble(result)));
}

// §20.8.2 (C2): $ln at the singular point 0 returns negative infinity, the same
// pole behavior as std::log.
TEST(SysTaskMath, LnOfZeroIsNegativeInfinity) {
  SysTaskMathFixture f;
  auto* expr = MkSysCall(f.arena, "$ln", {MkReal(f.arena, 0.0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  double d = ResultToDouble(result);
  EXPECT_TRUE(std::isinf(d));
  EXPECT_LT(d, 0.0);
}
