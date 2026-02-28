// §11.4.4: Relational operators


#include "simulator/eval.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Eval, Comparison) {
  ExprFixture f;
  auto* expr = ParseExprFrom("5 > 3", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

}  // namespace
