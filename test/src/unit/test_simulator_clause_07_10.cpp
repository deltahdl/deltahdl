// §7.10: Queues

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(QueueAccess, OutOfBoundsReturnsX) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 16);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 100));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 200));
  // In-bounds: q[1] should return 200.
  auto in_result = EvalExpr(MakeSelect(f.arena, "q", 1), f.ctx, f.arena);
  EXPECT_EQ(in_result.ToUint64(), 200u);
  EXPECT_TRUE(in_result.IsKnown());
  // Out-of-bounds: q[5] should return X.
  auto oob_result = EvalExpr(MakeSelect(f.arena, "q", 5), f.ctx, f.arena);
  EXPECT_FALSE(oob_result.IsKnown());
}

}  // namespace
