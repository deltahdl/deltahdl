// §20.8: Math functions

#include <gtest/gtest.h>

#include <cmath>
#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Helper: extract double from a Logic4Vec stored as IEEE 754 bits
// =============================================================================
static double VecToDouble(const Logic4Vec &vec) {
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

  Expr *MakeRealLiteral(double val) {
    auto *lit = arena.Create<Expr>();
    lit->kind = ExprKind::kRealLiteral;
    lit->real_val = val;
    return lit;
  }

  Expr *MakeIntLiteral(uint64_t val) {
    auto *lit = arena.Create<Expr>();
    lit->kind = ExprKind::kIntegerLiteral;
    lit->int_val = val;
    return lit;
  }

  Variable *CreateRealVar(std::string_view name, double val) {
    auto *var = ctx.CreateVariable(name, 64);
    uint64_t bits = 0;
    std::memcpy(&bits, &val, sizeof(double));
    var->value = MakeLogic4VecVal(arena, 64, bits);
    ctx.RegisterRealVariable(name);
    return var;
  }
};
namespace {

// =============================================================================
// §20.8: Math system calls with real args
// =============================================================================
TEST(RealTypes, MathSqrtReal) {
  RealFixture f;
  // $sqrt(4.0) should return 2.0.
  auto *call = f.arena.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = "$sqrt";
  call->args = {f.MakeRealLiteral(4.0)};
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), 2.0, 1e-10);
}

TEST(RealTypes, MathLnReal) {
  RealFixture f;
  // $ln(1.0) should return 0.0.
  auto *call = f.arena.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = "$ln";
  call->args = {f.MakeRealLiteral(1.0)};
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), 0.0, 1e-10);
}

}  // namespace
