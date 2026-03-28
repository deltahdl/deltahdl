#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/lowerer.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

// --- Helpers ---

// Build an Expr for "$".
Expr* MakeDollar(Arena& arena) { return MakeId(arena, "$"); }

// Build "$-1".
Expr* MakeDollarMinus1(Arena& arena) {
  return MakeBinary(arena, TokenKind::kMinus, MakeDollar(arena),
                    MakeInt(arena, 1));
}

// Build a queue slice expression: name[lo_expr : hi_expr].
Expr* MakeSlice(Arena& arena, std::string_view name, Expr* lo, Expr* hi) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = MakeId(arena, name);
  e->index = lo;
  e->index_end = hi;
  return e;
}

// Build a concatenation expression from a list of sub-expressions.
Expr* MakeConcat(Arena& arena, std::vector<Expr*> elems) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kConcatenation;
  e->elements = std::move(elems);
  return e;
}

// --- End-to-end: q = {} clears queue ---

TEST(QueueAssign, EmptyConcatClearsQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    q = {1, 2, 3};\n"
      "    q = {};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

// --- q = {q, 6} equivalent to push_back(6) ---

TEST(QueueAssign, ConcatAppendEquivPushBack) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  // q = {q, 6}
  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 6)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 6u);
}

// --- q = {e, q} equivalent to push_front(e) ---

TEST(QueueAssign, ConcatPrependEquivPushFront) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  // q = {5, q}
  auto* rhs = MakeConcat(f.arena, {MakeInt(f.arena, 5), MakeId(f.arena, "q")});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

// --- q = q[1:$] equivalent to pop_front / delete(0) ---

TEST(QueueAssign, SliceFromOneEquivPopFront) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  // q = q[1:$]
  auto* slice = MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollar(f.arena));
  auto* rhs = MakeConcat(f.arena, {slice});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

// --- q = q[0:$-1] equivalent to pop_back / delete(q.size-1) ---

TEST(QueueAssign, SliceToLastMinus1EquivPopBack) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  // q = q[0:$-1]
  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeDollarMinus1(f.arena));
  auto* rhs = MakeConcat(f.arena, {slice});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// --- q = {q[0:pos-1], e, q[pos:$]} equivalent to insert(pos, e) ---

TEST(QueueAssign, ConcatInsertAtPosEquivInsert) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40});
  // Insert 99 at position 2: q = {q[0:1], 99, q[2:$]}
  auto* left = MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeInt(f.arena, 1));
  auto* right = MakeSlice(f.arena, "q", MakeInt(f.arena, 2), MakeDollar(f.arena));
  auto* rhs = MakeConcat(f.arena, {left, MakeInt(f.arena, 99), right});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 5u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
  EXPECT_EQ(q->elements[4].ToUint64(), 40u);
}

// --- q = {q[0:pos], e, q[pos+1:$]} equivalent to insert(pos+1, e) ---

TEST(QueueAssign, ConcatInsertAfterPosEquivInsertPlus1) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40});
  // Insert 99 after position 1: q = {q[0:1], 99, q[2:$]}
  // This is the same shape as insert(2, 99).
  auto* left = MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeInt(f.arena, 1));
  auto* right = MakeSlice(f.arena, "q", MakeInt(f.arena, 2), MakeDollar(f.arena));
  auto* rhs = MakeConcat(f.arena, {left, MakeInt(f.arena, 99), right});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 5u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
  EXPECT_EQ(q->elements[4].ToUint64(), 40u);
}

// --- q = {} equivalent to delete() ---

TEST(QueueAssign, EmptyConcatEquivDelete) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  auto* rhs = MakeConcat(f.arena, {});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  EXPECT_EQ(q->elements.size(), 0u);
}

// --- q = q[2:$] — drop first two, no single-method equivalent ---

TEST(QueueAssign, SliceDropFirstTwo) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});
  // q = q[2:$]
  auto* slice = MakeSlice(f.arena, "q", MakeInt(f.arena, 2), MakeDollar(f.arena));
  auto* rhs = MakeConcat(f.arena, {slice});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 30u);
  EXPECT_EQ(q->elements[1].ToUint64(), 40u);
  EXPECT_EQ(q->elements[2].ToUint64(), 50u);
}

// --- q = q[1:$-1] — drop first and last, no single-method equivalent ---

TEST(QueueAssign, SliceDropFirstAndLast) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});
  // q = q[1:$-1]
  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollarMinus1(f.arena));
  auto* rhs = MakeConcat(f.arena, {slice});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
  EXPECT_EQ(q->elements[2].ToUint64(), 40u);
}

// --- Assignment outdates all element references ---

TEST(QueueAssign, ConcatAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto old_gen = q->generation;
  auto old_ids = q->element_ids;

  // q = {q, 40}
  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 40)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  EXPECT_GT(q->generation, old_gen);
  // All element_ids must be fresh (none match the old ones).
  for (size_t i = 0; i < old_ids.size() && i < q->element_ids.size(); ++i)
    EXPECT_NE(q->element_ids[i], old_ids[i]);
}

TEST(QueueAssign, SliceAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto old_gen = q->generation;

  // q = q[1:$]
  auto* slice = MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollar(f.arena));
  auto* rhs = MakeConcat(f.arena, {slice});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  EXPECT_GT(q->generation, old_gen);
}

// --- Edge cases ---

TEST(QueueAssign, ConcatAppendToEmptyQueue) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  // q = {q, 7}
  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 7)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 7u);
}

TEST(QueueAssign, ConcatPrependToEmptyQueue) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  // q = {7, q}
  auto* rhs = MakeConcat(f.arena, {MakeInt(f.arena, 7), MakeId(f.arena, "q")});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 7u);
}

TEST(QueueAssign, SlicePopFrontOnSingleElement) {
  SimFixture f;
  MakeQueue(f, "q", {42});
  // q = q[1:$] — only element removed, result is empty.
  auto* slice = MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollar(f.arena));
  auto* rhs = MakeConcat(f.arena, {slice});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueAssign, SlicePopBackOnSingleElement) {
  SimFixture f;
  MakeQueue(f, "q", {42});
  // q = q[0:$-1] — $=0, $-1=-1, a>b yields empty.
  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeDollarMinus1(f.arena));
  auto* rhs = MakeConcat(f.arena, {slice});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  auto* q = f.ctx.FindQueue("q");
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueAssign, AssignReplacesContents) {
  SimFixture f;
  auto* dst = MakeQueue(f, "dst", {1, 2, 3});
  MakeQueue(f, "src", {10, 20});

  auto* src = f.ctx.FindQueue("src");
  dst->elements = src->elements;
  dst->AssignFreshIds();

  ASSERT_EQ(dst->elements.size(), 2u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 10u);
  EXPECT_EQ(dst->elements[1].ToUint64(), 20u);
}

TEST(QueueAssign, AssignEmptyClears) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  q->elements.clear();
  q->element_ids.clear();
  EXPECT_EQ(q->elements.size(), 0u);
}

}  // namespace
