#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

// An integer literal carrying an x bit. The queue operators treat any index
// whose value has x or z bits as invalid, so this drives those paths.
Expr* MakeXLiteral(Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->text = "1'bx";
  return e;
}

// Builds a queue slice expression q[lo:hi].
Expr* MakeQueueSlice(Arena& arena, std::string_view base, Expr* lo, Expr* hi) {
  auto* slice = arena.Create<Expr>();
  slice->kind = ExprKind::kSelect;
  slice->base = MakeId(arena, base);
  slice->index = lo;
  slice->index_end = hi;
  return slice;
}

// Assigns {expr} into the queue named dst and applies the write.
void AssignSliceToDst(SimFixture& f, std::string_view dst, Expr* expr) {
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {expr};
  auto* stmt = MakeAssign(f.arena, dst, rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
}

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

  auto result = EvalExpr(MakeSelect(f.arena, "q", 0xFFFFFFFFu), f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

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
  auto before = f.diag.WarningCount();
  auto* lhs = MakeSelect(f.arena, "q", 5);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
  EXPECT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

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

TEST(QueueOps, SliceYieldsCorrectElements) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 1), MakeInt(f.arena, 3)));

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

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 2), MakeInt(f.arena, 0)));

  auto* dst = f.ctx.FindQueue("dst");
  EXPECT_EQ(dst->elements.size(), 0u);
}

TEST(QueueOps, SliceSingleElementYieldsOneItem) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 1), MakeInt(f.arena, 1)));

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 1u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
}

TEST(QueueOps, SliceBBeyondDollarClampsToDollar) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 1), MakeInt(f.arena, 100)));

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 2u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
  EXPECT_EQ(dst->elements[1].ToUint64(), 30u);
}

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

TEST(QueueOps, SliceFullRangeCopiesAll) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 0), MakeInt(f.arena, 2)));

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 3u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 10u);
  EXPECT_EQ(dst->elements[2].ToUint64(), 30u);
}

// A slice bound that is a 4-state value containing x/z yields the empty queue.
TEST(QueueOps, SliceXZBoundYieldsEmpty) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {99});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeXLiteral(f.arena), MakeInt(f.arena, 2)));

  auto* dst = f.ctx.FindQueue("dst");
  EXPECT_EQ(dst->elements.size(), 0u);
}

// q[a:b] with a < 0 behaves as q[0:b]: the low bound clamps up to 0.
TEST(QueueOps, SliceNegativeLowSameAsZero) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(f, "dst",
                   MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 0xFFFFFFFFu),
                                  MakeInt(f.arena, 2)));

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 3u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 10u);
  EXPECT_EQ(dst->elements[2].ToUint64(), 30u);
}

// q[n:n] with n outside the queue's range (here n > $) yields the empty queue.
TEST(QueueOps, SliceSingleOutOfRangeYieldsEmpty) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {99});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 5), MakeInt(f.arena, 5)));

  auto* dst = f.ctx.FindQueue("dst");
  EXPECT_EQ(dst->elements.size(), 0u);
}

// Writing to q[$+1] is legal: on an unbounded queue it grows by one element.
TEST(QueueOps, IndexedWriteDollarPlusOneGrowsQueue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* lhs = MakeSelect(f.arena, "q", 2);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  bool ok = TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_TRUE(ok);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
}

// An indexed write whose index is a 4-state value with x/z is ignored and a
// run-time warning is issued.
TEST(QueueOps, IndexedWriteXZIndexIgnored) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto before = f.diag.WarningCount();
  auto* lhs =
      MakeSelectExpr(f.arena, MakeId(f.arena, "q"), MakeXLiteral(f.arena));
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// A negative index lies outside 0...$+1, so the indexed write through it is
// ignored and a run-time warning is issued (the low-end counterpart of the
// out-of-bounds-high case).
TEST(QueueOps, NegativeIndexWriteIgnored) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto before = f.diag.WarningCount();
  auto* lhs = MakeSelect(f.arena, "q", 0xFFFFFFFFu);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// A read through an index that is a 4-state value with x/z is invalid and
// returns the value for a nonexistent element (x for a 4-state element type).
TEST(QueueOps, XZIndexReadReturnsX) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  auto* sel =
      MakeSelectExpr(f.arena, MakeId(f.arena, "q"), MakeXLiteral(f.arena));
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

}  // namespace
