// §11.4.8: Bitwise operators

#include "fixture_simulator.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(Eval, BitwiseAnd) {
  ExprFixture f;
  auto* expr = ParseExprFrom("15 & 6", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 6u);
}

}  // namespace
