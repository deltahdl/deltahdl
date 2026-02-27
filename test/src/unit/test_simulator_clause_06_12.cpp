// §6.12: Real, shortreal, and realtime data types


#include <cmath>
#include <cstring>

#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

// =============================================================================
// Helper: extract double from a Logic4Vec stored as IEEE 754 bits
// =============================================================================
static double VecToDouble(const Logic4Vec& vec) {
  uint64_t bits = vec.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

// =============================================================================
// Test fixture
// =============================================================================
struct RealFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  Expr* MakeRealLiteral(double val) {
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kRealLiteral;
    lit->real_val = val;
    return lit;
  }

  Expr* MakeIntLiteral(uint64_t val) {
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kIntegerLiteral;
    lit->int_val = val;
    return lit;
  }

  Variable* CreateRealVar(std::string_view name, double val) {
    auto* var = ctx.CreateVariable(name, 64);
    uint64_t bits = 0;
    std::memcpy(&bits, &val, sizeof(double));
    var->value = MakeLogic4VecVal(arena, 64, bits);
    ctx.RegisterRealVariable(name);
    return var;
  }
};
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

static double ToDouble(const Variable* var) {
  uint64_t bits = var->value.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  return d;
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
