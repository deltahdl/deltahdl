// §5.7.1: Integer literal constants

#include "fixture_simulator.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(Eval, IntegerLiteral) {
  ExprFixture f;
  auto* expr = ParseExprFrom("42", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

}  // namespace
