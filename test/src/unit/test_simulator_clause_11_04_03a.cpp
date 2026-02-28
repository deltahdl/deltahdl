// §11.4.3: Arithmetic operators

#include "fixture_simulator.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(Eval, Addition) {
  ExprFixture f;
  auto* expr = ParseExprFrom("10 + 32", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

}  // namespace
