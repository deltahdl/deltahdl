#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueueDelete, DeleteAtIndex) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 1)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueDelete, DeleteFirstElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 0)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueDelete, DeleteLastElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 2)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueDelete, DeleteOnlyElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {42});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 0)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueDelete, NoArgClearsAll) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueDelete, NoArgOnEmptyQueueIsNoop) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  auto* call = MakeMethodCall(f.arena, "q", "delete", {});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueDelete, PropertyStyleClearsAll) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  TryExecQueuePropertyStmt("q", "delete", f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueDelete, IndexEqualToSizeIsNoop) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 2)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueDelete, IndexGreaterThanSizeIsNoop) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* call =
      MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 100)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueDelete, XzIndexIsNoop) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* idx_var = f.ctx.CreateVariable("idx", 32);
  idx_var->value = MakeLogic4Vec(f.arena, 32);
  idx_var->value.words[0].aval = 0;
  idx_var->value.words[0].bval = 1;  // x value
  auto* call =
      MakeMethodCall(f.arena, "q", "delete", {MakeId(f.arena, "idx")});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueDelete, NegativeIndexIsNoop) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* idx_var = f.ctx.CreateVariable("idx", 32);
  idx_var->value = MakeLogic4Vec(f.arena, 32);
  idx_var->value.words[0].aval = static_cast<uint64_t>(-1);  // -1 as signed
  idx_var->value.words[0].bval = 0;
  idx_var->value.is_signed = true;
  auto* call =
      MakeMethodCall(f.arena, "q", "delete", {MakeId(f.arena, "idx")});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueDelete, DeleteOnEmptyQueueWithIndexIsNoop) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 0)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

}  // namespace
