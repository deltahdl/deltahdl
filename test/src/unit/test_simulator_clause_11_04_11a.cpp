// §11.4.11: Conditional operator


#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Eval, Ternary) {
  ExprFixture f;
  auto* expr = ParseExprFrom("1 ? 42 : 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

}  // namespace
