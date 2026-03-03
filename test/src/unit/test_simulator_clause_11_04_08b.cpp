// Non-LRM tests

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// ==========================================================================
// Additional edge cases
// ==========================================================================
TEST(EvalOp, ReductionAndZero) {
  SimFixture f;
  // &32'd0 = 0
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
