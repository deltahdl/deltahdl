// Non-LRM tests

#include "fixture_simulator.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AggregateExpr, PackedStructNotInSet) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("s", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 7);
  auto* expr = ParseExprFrom("s inside {5, 10, 15}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
