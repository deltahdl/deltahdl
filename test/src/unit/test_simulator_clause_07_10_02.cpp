#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueueMethods, SizeReturnsCount) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "size", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 3u);
}

TEST(QueueMethods, SizeReturnsZeroForEmpty) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "size", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(QueueMethods, InsertAtIndex) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 30});
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 1), MakeInt(f.arena, 20)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(QueueMethods, InsertOutOfRangeIsNoop) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 100), MakeInt(f.arena, 99)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);
}

TEST(QueueMethods, DeleteAtIndex) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 1)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueMethods, DeleteNoArgClearsAll) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueMethods, PopFrontReturnsFirst) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 10u);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
}

TEST(QueueMethods, PopFrontEmptyReturnsZero) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_front", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(QueueMethods, PopBackReturnsLast) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_back", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 30u);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueMethods, PopBackEmptyReturnsZero) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "pop_back", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(QueueMethods, PushFrontInsertsAtFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {20, 30});
  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 10)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueMethods, PushBackInsertsAtEnd) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 30)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

}  // namespace
