// §11.4.13: for an explanation of range list syntax.


#include "simulator/eval.h"
#include "simulator/eval_array.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// =============================================================================
// §11.2.2 Aggregate expressions — struct in set membership
// =============================================================================
TEST(AggregateExpr, PackedStructInsideSet) {
  // A packed struct is just a bitvector — inside should work by value.
  SimFixture f;
  auto* var = f.ctx.CreateVariable("s", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);
  auto* expr = ParseExprFrom("s inside {5, 10, 15}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(AggregateExpr, PackedStructNotInSet) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("s", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 7);
  auto* expr = ParseExprFrom("s inside {5, 10, 15}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
