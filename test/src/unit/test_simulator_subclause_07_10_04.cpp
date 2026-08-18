#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "helpers_queue_assign_assert.h"
#include "simulator/lowerer.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

Expr* MakeDollar(Arena& arena) { return MakeId(arena, "$"); }

Expr* MakeDollarMinus1(Arena& arena) {
  return MakeBinary(arena, TokenKind::kMinus, MakeDollar(arena),
                    MakeInt(arena, 1));
}

Expr* MakeSlice(Arena& arena, std::string_view name, Expr* lo, Expr* hi) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = MakeId(arena, name);
  e->index = lo;
  e->index_end = hi;
  return e;
}

Expr* MakeConcat(Arena& arena, std::vector<Expr*> elems) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kConcatenation;
  e->elements = std::move(elems);
  return e;
}

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

TEST(QueueAssign, ConcatAppendEquivPushBack) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 6)});
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {10, 20, 30, 6});
}

TEST(QueueAssign, ConcatPrependEquivPushFront) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* rhs = MakeConcat(f.arena, {MakeInt(f.arena, 5), MakeId(f.arena, "q")});
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {5, 10, 20, 30});
}

TEST(QueueAssign, SliceFromOneEquivPopFront) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollar(f.arena));
  AssignRhsToQueueQ(MakeConcat(f.arena, {slice}), f);

  ExpectQueueContents(f, "q", {20, 30});
}

TEST(QueueAssign, SliceToLastMinus1EquivPopBack) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeDollarMinus1(f.arena));
  AssignRhsToQueueQ(MakeConcat(f.arena, {slice}), f);

  ExpectQueueContents(f, "q", {10, 20});
}

TEST(QueueAssign, ConcatInsertAtPosEquivInsert) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40});

  auto* left =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeInt(f.arena, 1));
  auto* right =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 2), MakeDollar(f.arena));
  auto* rhs = MakeConcat(f.arena, {left, MakeInt(f.arena, 99), right});
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {10, 20, 99, 30, 40});
}

TEST(QueueAssign, EmptyConcatEquivDelete) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  AssignRhsToQueueQ(MakeConcat(f.arena, {}), f);

  ExpectQueueContents(f, "q", {});
}

TEST(QueueAssign, SliceDropFirstTwo) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});

  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 2), MakeDollar(f.arena));
  AssignRhsToQueueQ(MakeConcat(f.arena, {slice}), f);

  ExpectQueueContents(f, "q", {30, 40, 50});
}

TEST(QueueAssign, SliceDropFirstAndLast) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});

  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollarMinus1(f.arena));
  AssignRhsToQueueQ(MakeConcat(f.arena, {slice}), f);

  ExpectQueueContents(f, "q", {20, 30, 40});
}

TEST(QueueAssign, ConcatAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto old_gen = q->generation;
  auto old_ids = q->element_ids;

  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 40)});
  AssignRhsToQueueQ(rhs, f);

  EXPECT_GT(q->generation, old_gen);

  for (size_t i = 0; i < old_ids.size() && i < q->element_ids.size(); ++i)
    EXPECT_NE(q->element_ids[i], old_ids[i]);
}

TEST(QueueAssign, SliceAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto old_gen = q->generation;

  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollar(f.arena));
  AssignRhsToQueueQ(MakeConcat(f.arena, {slice}), f);

  EXPECT_GT(q->generation, old_gen);
}

TEST(QueueAssign, ConcatAppendToEmptyQueue) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);

  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 7)});
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {7});
}

TEST(QueueAssign, ConcatPrependToEmptyQueue) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);

  auto* rhs = MakeConcat(f.arena, {MakeInt(f.arena, 7), MakeId(f.arena, "q")});
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {7});
}

TEST(QueueAssign, SlicePopFrontOnSingleElement) {
  SimFixture f;
  MakeQueue(f, "q", {42});

  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollar(f.arena));
  AssignRhsToQueueQ(MakeConcat(f.arena, {slice}), f);

  ExpectQueueContents(f, "q", {});
}

TEST(QueueAssign, SlicePopBackOnSingleElement) {
  SimFixture f;
  MakeQueue(f, "q", {42});

  auto* slice =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeDollarMinus1(f.arena));
  AssignRhsToQueueQ(MakeConcat(f.arena, {slice}), f);

  ExpectQueueContents(f, "q", {});
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

// The LRM writes the pop_front-equivalent form as a bare slice assigned
// directly to the queue (q = q[1:$]), not wrapped in a concatenation. This
// drives the top-level slice branch of the assignment collector.
TEST(QueueAssign, BareSliceFromOneEquivPopFront) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* rhs = MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollar(f.arena));
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {20, 30});
}

// Bare slice form of the pop_back equivalent: q = q[0:$-1].
TEST(QueueAssign, BareSliceToLastMinus1EquivPopBack) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* rhs =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeDollarMinus1(f.arena));
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {10, 20});
}

// Bare slice form yielding a new queue lacking the first two items: q = q[2:$].
TEST(QueueAssign, BareSliceDropFirstTwo) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});

  auto* rhs = MakeSlice(f.arena, "q", MakeInt(f.arena, 2), MakeDollar(f.arena));
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {30, 40, 50});
}

// Bare slice form yielding a new queue lacking first and last: q = q[1:$-1].
TEST(QueueAssign, BareSliceDropFirstAndLast) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});

  auto* rhs =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollarMinus1(f.arena));
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {20, 30, 40});
}

// Second insert example: q = {q[0:pos], e, q[pos+1:$]} mirrors insert(pos+1,
// e). With pos = 2 the new element lands after index 2, distinct from the
// q[0:pos-1]/q[pos:$] form above.
TEST(QueueAssign, ConcatInsertAfterPosEquivInsertPlus1) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40});

  auto* left =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeInt(f.arena, 2));
  auto* right =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 3), MakeDollar(f.arena));
  auto* rhs = MakeConcat(f.arena, {left, MakeInt(f.arena, 99), right});
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {10, 20, 30, 99, 40});
}

// The tests above build each right-hand side as an AST and hand it straight to
// TryQueueBlockingAssign, which says nothing about whether a source file
// written the way §7.10.4 writes it reaches that function. The tests below
// state each of the subclause's forms as SystemVerilog, starting from the
// declaration the subclause itself uses, `int q[$] = { 2, 4, 8 };`.

// §7.10.4: `q = { q, 6 }` leaves what `q.push_back(6)` would leave.
TEST(QueueAssign, SourceConcatAppendEquivPushBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q = {q, 6};\n"
      "endmodule\n",
      "q", {2, 4, 8, 6});
}

// §7.10.4: `q = { e, q }` leaves what `q.push_front(e)` would leave.
TEST(QueueAssign, SourceConcatPrependEquivPushFront) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  int e = 6;\n"
      "  initial q = {e, q};\n"
      "endmodule\n",
      "q", {6, 2, 4, 8});
}

// §7.10.4: `q = q[1:$]` leaves what `q.pop_front()` or `q.delete(0)` would
// leave. The right-hand side reads the queue it is assigned to, so the
// elements it names have to be taken before the assignment writes.
TEST(QueueAssign, SourceSliceFromOneEquivPopFront) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q = q[1:$];\n"
      "endmodule\n",
      "q", {4, 8});
}

// §7.10.4: `q = q[0:$-1]` leaves what `q.pop_back()` or
// `q.delete(q.size-1)` would leave.
TEST(QueueAssign, SourceSliceToLastMinusOneEquivPopBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q = q[0:$-1];\n"
      "endmodule\n",
      "q", {2, 4});
}

// §7.10.4: `q = { q[0:pos-1], e, q[pos:$] }` leaves what `q.insert(pos, e)`
// would leave. `pos` is a variable, which is what §7.10.1 means by saying the
// slice bounds "may be arbitrary integral expressions and, in particular, are
// not required to be constant expressions".
TEST(QueueAssign, SourceConcatInsertAtPosEquivInsert) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  int e = 6;\n"
      "  int pos = 1;\n"
      "  initial q = {q[0:pos-1], e, q[pos:$]};\n"
      "endmodule\n",
      "q", {2, 6, 4, 8});
}

// §7.10.4: `q = { q[0:pos], e, q[pos+1:$] }` leaves what `q.insert(pos+1, e)`
// would leave, one place later than the form above from the same `pos`.
TEST(QueueAssign, SourceConcatInsertAfterPosEquivInsertPlusOne) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  int e = 6;\n"
      "  int pos = 1;\n"
      "  initial q = {q[0:pos], e, q[pos+1:$]};\n"
      "endmodule\n",
      "q", {2, 4, 6, 8});
}

// §7.10.4: `q = q[2:$]` is "a new queue lacking the first two items".
TEST(QueueAssign, SourceSliceDropsFirstTwo) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8, 16, 32};\n"
      "  initial q = q[2:$];\n"
      "endmodule\n",
      "q", {8, 16, 32});
}

// §7.10.4: `q = q[1:$-1]` is "a new queue lacking the first and last items".
TEST(QueueAssign, SourceSliceDropsFirstAndLast) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8, 16, 32};\n"
      "  initial q = q[1:$-1];\n"
      "endmodule\n",
      "q", {4, 8, 16});
}

// §7.10.3: "any reference to elements of the queue will become outdated by the
// assignment operation". A reference taken after the assignment is not one of
// those, so it still writes back.
TEST(QueueAssign, SourceRefTakenAfterAssignWritesBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  function automatic void set_ref(ref int v);\n"
      "    v = 99;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q = {q, 6};\n"
      "    set_ref(q[1]);\n"
      "  end\n"
      "endmodule\n",
      "q", {2, 99, 8, 6});
}

// §7.10.4 with §10.4.2: a nonblocking assignment updates the queue variable in
// the same nine forms a blocking one does. Its right-hand side is evaluated
// where the statement stands and the queue is written in the NBA region, which
// changes when the queue changes and not what it is left holding.
TEST(QueueAssignNba, ConcatAppendEquivPushBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q <= {q, 6};\n"
      "endmodule\n",
      "q", {2, 4, 8, 6});
}

// §7.10.4: the nonblocking spelling of `q = { e, q }`.
TEST(QueueAssignNba, ConcatPrependEquivPushFront) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  int e = 6;\n"
      "  initial q <= {e, q};\n"
      "endmodule\n",
      "q", {6, 2, 4, 8});
}

// §7.10.4: the nonblocking spelling of `q = q[1:$]`. The right-hand side is a
// slice and carries no braces, so a queue path that recognizes only a
// concatenation reads it as the one value its elements concatenate to.
TEST(QueueAssignNba, SliceFromOneEquivPopFront) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q <= q[1:$];\n"
      "endmodule\n",
      "q", {4, 8});
}

// §7.10.4: the nonblocking spelling of `q = q[0:$-1]`.
TEST(QueueAssignNba, SliceToLastMinusOneEquivPopBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q <= q[0:$-1];\n"
      "endmodule\n",
      "q", {2, 4});
}

// §7.10.4: the nonblocking spelling of `q = { q[0:pos-1], e, q[pos:$] }`. A
// slice written as an item of the concatenation contributes the run of
// elements it names, not the single value they concatenate to.
TEST(QueueAssignNba, ConcatInsertAtPosEquivInsert) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  int e = 6;\n"
      "  int pos = 1;\n"
      "  initial q <= {q[0:pos-1], e, q[pos:$]};\n"
      "endmodule\n",
      "q", {2, 6, 4, 8});
}

// §7.10.4: the nonblocking spelling of `q = q[2:$]`.
TEST(QueueAssignNba, SliceDropsFirstTwo) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8, 16, 32};\n"
      "  initial q <= q[2:$];\n"
      "endmodule\n",
      "q", {8, 16, 32});
}

// §7.10.4: the nonblocking spelling of `q = q[1:$-1]`.
TEST(QueueAssignNba, SliceDropsFirstAndLast) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8, 16, 32};\n"
      "  initial q <= q[1:$-1];\n"
      "endmodule\n",
      "q", {4, 8, 16});
}

// §7.10.4: the nonblocking spelling of `q = {}`, which §7.10 makes the empty
// queue.
TEST(QueueAssignNba, EmptyConcatClearsQueue) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q <= {};\n"
      "endmodule\n",
      "q", {});
}

// §10.4.2: the right-hand side of a nonblocking assignment is evaluated when
// the statement executes, so both statements below read the queue the
// declaration left and the second one's value is what the NBA region writes.
// A right-hand side evaluated in the NBA region instead would append 4 and
// then append 5 to the result, leaving five elements.
TEST(QueueAssignNba, RhsReadsQueueWhereTheStatementStands) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial begin\n"
      "    q <= {q, 4};\n"
      "    q <= {q, 5};\n"
      "  end\n"
      "endmodule\n",
      "q", {2, 4, 8, 5});
}

// §7.10.3: a nonblocking assignment to the queue variable outdates the
// references the queue held, and leaves the queue able to record a reference
// taken afterwards. A path that dropped the element identities rather than
// replacing them would leave this write-back with nothing to land on.
TEST(QueueAssignNba, RefTakenAfterAssignWritesBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  function automatic void set_ref(ref int v);\n"
      "    v = 99;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q <= {q, 6};\n"
      "    #1 set_ref(q[1]);\n"
      "  end\n"
      "endmodule\n",
      "q", {2, 99, 8, 6});
}

}  // namespace
