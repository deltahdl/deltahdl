#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueuePushBack, InsertsAtEnd) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 30)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(QueuePushBack, OnEmptyQueue) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 42)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

TEST(QueuePushBack, PreservesExistingOrder) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30, 40});
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 50)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 5u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 40u);
  EXPECT_EQ(q->elements[4].ToUint64(), 50u);
}

TEST(QueuePushBack, IncrementsGeneration) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  uint32_t gen_before = q->generation;
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 30)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->generation, gen_before + 1);
}

TEST(QueuePushBack, MultiplePushesAccumulateAtEnd) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  for (int i = 1; i <= 3; ++i) {
    auto* call = MakeMethodCall(f.arena, "q", "push_back",
                                {MakeInt(f.arena, static_cast<uint64_t>(i))});
    TryExecQueueMethodStmt(call, f.ctx, f.arena);
  }
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 1u);
  EXPECT_EQ(q->elements[1].ToUint64(), 2u);
  EXPECT_EQ(q->elements[2].ToUint64(), 3u);
}

}  // namespace
