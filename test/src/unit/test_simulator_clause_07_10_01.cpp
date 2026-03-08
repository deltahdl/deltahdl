#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueueOps, IndexReturnsElement) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  auto result = EvalExpr(MakeSelect(f.arena, "q", 1), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

TEST(QueueOps, OutOfBoundsReturnsX) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  auto result = EvalExpr(MakeSelect(f.arena, "q", 5), f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(QueueOps, EmptyQueueSizeZero) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  EXPECT_EQ(q->elements.size(), 0u);
}

}
