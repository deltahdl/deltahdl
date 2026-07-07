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

// §7.10.1: an invalid queue index causes the read to return the value
// appropriate for a nonexistent element of the queue's element type, as
// specified by Table 7-1 in §7.4.5. For a 2-state element type (int) that value
// is a known '0, not x. The queue and its element type are built from real
// source so the 2-state-ness that selects the Table 7-1 row is produced by the
// declaration rather than hand-set.
TEST(QueueOps, OutOfBoundsReadOfTwoStateQueueYieldsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{10, 20, 30};\n"
      "  logic [31:0] res;\n"
      "  initial res = q[5];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* res = f.ctx.FindVariable("res");
  ASSERT_NE(res, nullptr);
  EXPECT_TRUE(res->value.IsKnown());
  EXPECT_EQ(res->value.ToUint64(), 0u);
}

// The 4-state counterpart: an out-of-bounds read of a 4-state (logic) queue
// yields x, the Table 7-1 value for a 4-state element type. Same source-built
// setup as the 2-state case; only the declared element type differs, so the
// difference in result must come from the queue's element-type state-ness.
TEST(QueueOps, OutOfBoundsReadOfFourStateQueueYieldsX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q[$] = '{10, 20, 30};\n"
      "  logic [7:0] res;\n"
      "  initial res = q[5];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* res = f.ctx.FindVariable("res");
  ASSERT_NE(res, nullptr);
  EXPECT_FALSE(res->value.IsKnown());
}

// An index expression carrying x/z bits is an invalid index just as an
// out-of-bounds position is; on a 2-state queue the read still yields the
// Table 7-1 value '0. Driven from source: the x index is produced by assigning
// an x literal to a variable used to index the queue.
TEST(QueueOps, UnknownIndexReadOfTwoStateQueueYieldsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{10, 20, 30};\n"
      "  logic [31:0] idx;\n"
      "  logic [31:0] res;\n"
      "  initial begin\n"
      "    idx = 32'bx;\n"
      "    res = q[idx];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* res = f.ctx.FindVariable("res");
  ASSERT_NE(res, nullptr);
  EXPECT_TRUE(res->value.IsKnown());
  EXPECT_EQ(res->value.ToUint64(), 0u);
}

// §7.10.1: in a queue slice q[a:b], the bounds may be arbitrary integral
// expressions and are NOT required to be constant — the distinguishing
// relaxation of queues versus the fixed-size array slice/part-select of §7.4.5,
// whose size must be constant. The slice bounds here are runtime variables
// assigned at simulation time, and the whole flow (declare, initialize, slice,
// observe) is driven from source so the non-constant-ness of the bounds is
// genuinely produced rather than asserted.
TEST(QueueOps, SliceBoundsMayBeRuntimeVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{10, 20, 30, 40, 50};\n"
      "  int dst[$];\n"
      "  int lo, hi;\n"
      "  initial begin\n"
      "    lo = 1;\n"
      "    hi = 3;\n"
      "    dst = q[lo:hi];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_NE(dst, nullptr);
  ASSERT_EQ(dst->elements.size(), 3u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
  EXPECT_EQ(dst->elements[1].ToUint64(), 30u);
  EXPECT_EQ(dst->elements[2].ToUint64(), 40u);
}

// §7.10.1: a queue declared with a right bound (a bounded queue) shall be
// limited so its size does not exceed N+1. Built from real source: the bound is
// produced by the `[$:2]` declaration (N=2, so at most 3 elements), and an
// assignment of five values through the full pipeline is truncated to the
// limit.
TEST(QueueOps, BoundedQueueFromSourceLimitsSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$:2];\n"
      "  initial q = {1, 2, 3, 4, 5};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 3u);
}

// End-to-end via the §10.9 dependency: a queue value may be written using an
// assignment pattern. The queue is initialized from `'{...}` in real source and
// the resulting elements are read back through indexed reads.
TEST(QueueOps, QueueInitializedByAssignmentPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{11, 22, 33};\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    a = q[0];\n"
      "    b = q[1];\n"
      "    c = q[2];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 22u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 33u);
}

// End-to-end via the §10.10 dependency: a queue value may be written using an
// unpacked array concatenation. Assigning `{...}` in real source grows the
// queue to hold the concatenated elements, which are then observed directly.
TEST(QueueOps, QueueValueFromUnpackedArrayConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {44, 55, 66};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 44u);
  EXPECT_EQ(q->elements[1].ToUint64(), 55u);
  EXPECT_EQ(q->elements[2].ToUint64(), 66u);
}

}  // namespace
