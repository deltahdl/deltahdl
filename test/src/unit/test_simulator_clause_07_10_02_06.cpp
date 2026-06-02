#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueuePushFront, InsertsAtFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {20, 30});
  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 10)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(QueuePushFront, OnEmptyQueue) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 42)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

TEST(QueuePushFront, IncrementsGeneration) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  uint32_t gen_before = q->generation;
  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 5)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->generation, gen_before + 1);
}

TEST(QueuePushFront, IsVoidStatementFormMethod) {
  // The prototype is `function void push_front(input element_t item)`: the
  // method yields no value, so it is dispatched through the void statement
  // path, which reports that it handled the call. The single element_t
  // argument is the element placed at the front.
  SimFixture f;
  auto* q = MakeQueue(f, "q", {20});
  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 7)});
  bool handled = TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_TRUE(handled);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 7u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueuePushFront, WithoutElementArgumentIsNotApplied) {
  // The prototype mandates one `input element_t item`. A call lacking the
  // element argument does not match push_front, so the statement dispatcher
  // declines to handle it and the queue is left unchanged.
  SimFixture f;
  auto* q = MakeQueue(f, "q", {20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "push_front", {});
  bool handled = TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_FALSE(handled);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueuePushFront, MultiplePushesAccumulateAtFront) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  for (int i = 1; i <= 3; ++i) {
    auto* call = MakeMethodCall(f.arena, "q", "push_front",
                                {MakeInt(f.arena, static_cast<uint64_t>(i))});
    TryExecQueueMethodStmt(call, f.ctx, f.arena);
  }
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 3u);
  EXPECT_EQ(q->elements[1].ToUint64(), 2u);
  EXPECT_EQ(q->elements[2].ToUint64(), 1u);
}

}
