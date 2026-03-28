#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

// --- Indexing (Q[i]) ---

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

TEST(QueueOps, IndexFirstElement) {
  SimFixture f;
  MakeQueue(f, "q", {42, 99});
  auto result = EvalExpr(MakeSelect(f.arena, "q", 0), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(QueueOps, IndexLastElement) {
  SimFixture f;
  MakeQueue(f, "q", {42, 99, 7});
  auto result = EvalExpr(MakeSelect(f.arena, "q", 2), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

TEST(QueueOps, NegativeIndexReturnsX) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  // Use a large unsigned value that sign-extends to negative.
  auto result =
      EvalExpr(MakeSelect(f.arena, "q", 0xFFFFFFFFu), f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

// --- Indexed write (Q[i] = val) ---

TEST(QueueOps, IndexedWriteUpdatesElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* lhs = MakeSelect(f.arena, "q", 1);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 55);
  bool ok = TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_TRUE(ok);
  EXPECT_EQ(q->elements[1].ToUint64(), 55u);
}

TEST(QueueOps, IndexedWriteOutOfBoundsIgnored) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* lhs = MakeSelect(f.arena, "q", 5);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// --- Queue resize on assignment ---

TEST(QueueOps, AssignGrowsQueue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10});
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {MakeInt(f.arena, 1), MakeInt(f.arena, 2),
                   MakeInt(f.arena, 3)};
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
}

TEST(QueueOps, AssignShrinksQueue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30, 40});
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {MakeInt(f.arena, 5)};
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
}

// --- Slice (Q[a:b]) ---

TEST(QueueOps, SliceYieldsCorrectElements) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});
  MakeQueue(f, "dst", {});

  // dst = q[1:3] — should yield {20, 30, 40}.
  auto* slice = f.arena.Create<Expr>();
  slice->kind = ExprKind::kSelect;
  slice->base = MakeId(f.arena, "q");
  slice->index = MakeInt(f.arena, 1);
  slice->index_end = MakeInt(f.arena, 3);
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {slice};
  auto* stmt = MakeAssign(f.arena, "dst", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 3u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
  EXPECT_EQ(dst->elements[1].ToUint64(), 30u);
  EXPECT_EQ(dst->elements[2].ToUint64(), 40u);
}

TEST(QueueOps, SliceAGreaterThanBYieldsEmpty) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {99});

  // dst = q[2:0] — a > b, should yield empty queue.
  auto* slice = f.arena.Create<Expr>();
  slice->kind = ExprKind::kSelect;
  slice->base = MakeId(f.arena, "q");
  slice->index = MakeInt(f.arena, 2);
  slice->index_end = MakeInt(f.arena, 0);
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {slice};
  auto* stmt = MakeAssign(f.arena, "dst", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* dst = f.ctx.FindQueue("dst");
  EXPECT_EQ(dst->elements.size(), 0u);
}

TEST(QueueOps, SliceSingleElementYieldsOneItem) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  // dst = q[1:1] — should yield {20}.
  auto* slice = f.arena.Create<Expr>();
  slice->kind = ExprKind::kSelect;
  slice->base = MakeId(f.arena, "q");
  slice->index = MakeInt(f.arena, 1);
  slice->index_end = MakeInt(f.arena, 1);
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {slice};
  auto* stmt = MakeAssign(f.arena, "dst", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 1u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
}

TEST(QueueOps, SliceBBeyondDollarClampsToDollar) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  // dst = q[1:100] — b > $, should be same as q[1:$] = {20, 30}.
  auto* slice = f.arena.Create<Expr>();
  slice->kind = ExprKind::kSelect;
  slice->base = MakeId(f.arena, "q");
  slice->index = MakeInt(f.arena, 1);
  slice->index_end = MakeInt(f.arena, 100);
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {slice};
  auto* stmt = MakeAssign(f.arena, "dst", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 2u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
  EXPECT_EQ(dst->elements[1].ToUint64(), 30u);
}

// --- Bounded queue ([$:N]) ---

TEST(QueueOps, BoundedQueueAssignTruncates) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {MakeInt(f.arena, 1), MakeInt(f.arena, 2),
                   MakeInt(f.arena, 3), MakeInt(f.arena, 4),
                   MakeInt(f.arena, 5)};
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
}

// --- Empty queue ---

TEST(QueueOps, EmptyQueueReadReturnsX) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  auto result = EvalExpr(MakeSelect(f.arena, "q", 0), f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(QueueOps, EmptyQueueAssignEmptyConcat) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {};
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

// --- Slice with full range ---

TEST(QueueOps, SliceFullRangeCopiesAll) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  // dst = q[0:2] — full range, should copy all elements.
  auto* slice = f.arena.Create<Expr>();
  slice->kind = ExprKind::kSelect;
  slice->base = MakeId(f.arena, "q");
  slice->index = MakeInt(f.arena, 0);
  slice->index_end = MakeInt(f.arena, 2);
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {slice};
  auto* stmt = MakeAssign(f.arena, "dst", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 3u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 10u);
  EXPECT_EQ(dst->elements[2].ToUint64(), 30u);
}

}  // namespace
