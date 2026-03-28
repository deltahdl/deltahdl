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

TEST(QueuePopFront, EmptyQueueReturnsAllX) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_TRUE(HasUnknownBits(out));
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
