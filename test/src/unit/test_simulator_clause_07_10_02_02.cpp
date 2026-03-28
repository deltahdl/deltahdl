#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

TEST(QueueMethods, InsertAtFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 0), MakeInt(f.arena, 10)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(QueueMethods, InsertAtEnd) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 2), MakeInt(f.arena, 30)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(QueueMethods, InsertIntoEmptyQueue) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 0), MakeInt(f.arena, 42)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

TEST(QueueMethods, InsertOutOfRangeIsNoop) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 100), MakeInt(f.arena, 99)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);
}

TEST(QueueMethods, InsertWithXzIndexIsNoop) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* idx_var = f.ctx.CreateVariable("idx", 32);
  idx_var->value = MakeLogic4Vec(f.arena, 32);
  idx_var->value.words[0].aval = 0;
  idx_var->value.words[0].bval = 1;  // x value
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeId(f.arena, "idx"), MakeInt(f.arena, 99)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueMethods, InsertWithNegativeIndexIsNoop) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* idx_var = f.ctx.CreateVariable("idx", 32);
  idx_var->value = MakeLogic4Vec(f.arena, 32);
  idx_var->value.words[0].aval = static_cast<uint64_t>(-1);  // -1 as signed
  idx_var->value.words[0].bval = 0;
  idx_var->value.is_signed = true;
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeId(f.arena, "idx"), MakeInt(f.arena, 99)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

}  // namespace
