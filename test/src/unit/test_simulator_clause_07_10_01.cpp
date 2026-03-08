#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §7.10.1: Queue indexing returns correct element.
TEST(QueueOps, IndexReturnsElement) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  auto result = EvalExpr(MakeSelect(f.arena, "q", 1), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

// §7.10.1: Out-of-bounds index returns x.
TEST(QueueOps, OutOfBoundsReturnsX) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  auto result = EvalExpr(MakeSelect(f.arena, "q", 5), f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

// §7.10.1: Empty queue is valid.
TEST(QueueOps, EmptyQueueSizeZero) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  EXPECT_EQ(q->elements.size(), 0u);
}

}  // namespace
