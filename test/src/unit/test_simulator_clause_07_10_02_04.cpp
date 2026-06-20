#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueuePopFront, ReturnsFirstElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 10u);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueuePopFront, SingleElementLeavesEmpty) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {42});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 42u);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueuePopFront, EmptyFourStateQueueReturnsAllX) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32, /*max_size=*/-1, /*is_4state=*/true);
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_TRUE(HasUnknownBits(out));
}

// An empty queue of a 2-state element type yields the nonexistent-element
// value for that type per Table 7-1 (see 7.4.5): all-zero, not x.
TEST(QueuePopFront, EmptyTwoStateQueueReturnsZero) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32, /*max_size=*/-1, /*is_4state=*/false);
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_FALSE(HasUnknownBits(out));
  EXPECT_EQ(out.ToUint64(), 0u);
}

// The prototype returns element_t, so the popped value is sized to the
// queue's element type rather than a fixed width.
TEST(QueuePopFront, ReturnsValueSizedToElementType) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 8);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 8, 0xAB));
  q->AssignFreshIds();
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 8u);
  EXPECT_EQ(out.ToUint64(), 0xABu);
}

// The empty-queue return value is also sized to the element type (Table 7-1,
// see 7.4.5), here observed at a non-default element width.
TEST(QueuePopFront, EmptyQueueReturnSizedToElementType) {
  SimFixture f;
  f.ctx.CreateQueue("q", 8, /*max_size=*/-1, /*is_4state=*/true);
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 8u);
  EXPECT_TRUE(HasUnknownBits(out));
}

// Successive calls drain elements front-to-back; once the queue is empty the
// next call yields the nonexistent-element value and the queue stays empty.
TEST(QueuePopFront, RepeatedCallsDrainInOrderThenReturnNonexistent) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {1, 2, 3});
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  Logic4Vec out{};
  for (uint64_t expected : {1u, 2u, 3u}) {
    ASSERT_TRUE(TryEvalQueueMethodCall(call, f.ctx, f.arena, out));
    EXPECT_EQ(out.ToUint64(), expected);
  }
  ASSERT_EQ(q->elements.size(), 0u);
  ASSERT_TRUE(TryEvalQueueMethodCall(call, f.ctx, f.arena, out));
  EXPECT_TRUE(HasUnknownBits(out));
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueuePopFront, EmptyQueueRemainsEmpty) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  Logic4Vec out{};
  TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueuePopFront, IncrementsGeneration) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  uint32_t gen_before = q->generation;
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  EXPECT_EQ(q->generation, gen_before + 1);
}

TEST(QueuePopFront, EmptyQueueDoesNotIncrementGeneration) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  uint32_t gen_before = q->generation;
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  EXPECT_EQ(q->generation, gen_before);
}

}  // namespace
