// §6.12: Real, shortreal, and realtime data types

#include <cmath>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "fixture_real.h"
#include "helpers_eval_op.h"

using namespace delta;

namespace {

// =============================================================================
// §6.12: Real literal evaluation
// =============================================================================
TEST(RealTypes, RealLiteralEval) {
  RealFixture f;
  auto* lit = f.MakeRealLiteral(3.14);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), 3.14, 1e-10);
}

TEST(RealTypes, RealLiteralZero) {
  RealFixture f;
  auto* lit = f.MakeRealLiteral(0.0);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_EQ(VecToDouble(result), 0.0);
}

TEST(RealTypes, RealLiteralNegative) {
  RealFixture f;
  auto* lit = f.MakeRealLiteral(-2.5);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), -2.5, 1e-10);
}

// =============================================================================
// §6.12: Real variable storage
// =============================================================================
TEST(RealTypes, RealVarStorage) {
  RealFixture f;
  f.CreateRealVar("x", 1.5);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 1.5, 1e-10);
}

TEST(RealTypes, IsRealVariable) {
  RealFixture f;
  f.CreateRealVar("r", 0.0);
  EXPECT_TRUE(f.ctx.IsRealVariable("r"));
  f.ctx.CreateVariable("i", 32);
  EXPECT_FALSE(f.ctx.IsRealVariable("i"));
}

// § number — real_number simulates
TEST(SimA87, NumberReal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 3.14;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 3.14);
}

}  // namespace
