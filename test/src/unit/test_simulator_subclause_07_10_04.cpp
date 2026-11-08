#include <gtest/gtest.h>

#include <cstddef>
#include <utility>
#include <vector>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_queue.h"
#include "helpers_queue_assign_assert.h"
#include "helpers_scheduler.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
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

TEST(QueueAssign, BareSliceFromOneEquivPopFront) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* rhs = MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollar(f.arena));
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {20, 30});
}

TEST(QueueAssign, BareSliceToLastMinus1EquivPopBack) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* rhs =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 0), MakeDollarMinus1(f.arena));
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {10, 20});
}

TEST(QueueAssign, BareSliceDropFirstTwo) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});

  auto* rhs = MakeSlice(f.arena, "q", MakeInt(f.arena, 2), MakeDollar(f.arena));
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {30, 40, 50});
}

TEST(QueueAssign, BareSliceDropFirstAndLast) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});

  auto* rhs =
      MakeSlice(f.arena, "q", MakeInt(f.arena, 1), MakeDollarMinus1(f.arena));
  AssignRhsToQueueQ(rhs, f);

  ExpectQueueContents(f, "q", {20, 30, 40});
}

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

TEST(QueueAssign, SourceConcatAppendEquivPushBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q = {q, 6};\n"
      "endmodule\n",
      "q", {2, 4, 8, 6});
}

TEST(QueueAssign, SourceConcatPrependEquivPushFront) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  int e = 6;\n"
      "  initial q = {e, q};\n"
      "endmodule\n",
      "q", {6, 2, 4, 8});
}

TEST(QueueAssign, SourceSliceFromOneEquivPopFront) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q = q[1:$];\n"
      "endmodule\n",
      "q", {4, 8});
}

TEST(QueueAssign, SourceSliceToLastMinusOneEquivPopBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q = q[0:$-1];\n"
      "endmodule\n",
      "q", {2, 4});
}

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

TEST(QueueAssign, SourceSliceDropsFirstTwo) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8, 16, 32};\n"
      "  initial q = q[2:$];\n"
      "endmodule\n",
      "q", {8, 16, 32});
}

TEST(QueueAssign, SourceSliceDropsFirstAndLast) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8, 16, 32};\n"
      "  initial q = q[1:$-1];\n"
      "endmodule\n",
      "q", {4, 8, 16});
}

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

TEST(QueueAssignNba, ConcatAppendEquivPushBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q <= {q, 6};\n"
      "endmodule\n",
      "q", {2, 4, 8, 6});
}

TEST(QueueAssignNba, ConcatPrependEquivPushFront) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  int e = 6;\n"
      "  initial q <= {e, q};\n"
      "endmodule\n",
      "q", {6, 2, 4, 8});
}

TEST(QueueAssignNba, SliceFromOneEquivPopFront) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q <= q[1:$];\n"
      "endmodule\n",
      "q", {4, 8});
}

TEST(QueueAssignNba, SliceToLastMinusOneEquivPopBack) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q <= q[0:$-1];\n"
      "endmodule\n",
      "q", {2, 4});
}

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

TEST(QueueAssignNba, SliceDropsFirstTwo) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8, 16, 32};\n"
      "  initial q <= q[2:$];\n"
      "endmodule\n",
      "q", {8, 16, 32});
}

TEST(QueueAssignNba, SliceDropsFirstAndLast) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8, 16, 32};\n"
      "  initial q <= q[1:$-1];\n"
      "endmodule\n",
      "q", {4, 8, 16});
}

TEST(QueueAssignNba, EmptyConcatClearsQueue) {
  RunAndExpectQueue(
      "module t;\n"
      "  int q[$] = {2, 4, 8};\n"
      "  initial q <= {};\n"
      "endmodule\n",
      "q", {});
}

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

TEST(QueueAssign, SourceConcatItemOutOfRangeIndexContributesX) {
  SimFixture f;
  ElaborateLowerRun(f,
                    "module t;\n"
                    "  logic [31:0] q[$] = '{10, 20, 30};\n"
                    "  initial q = {q[5], 1};\n"
                    "endmodule\n");
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_FALSE(q->elements[0].IsKnown());
  EXPECT_EQ(q->elements[1].ToUint64(), 1u);
}

TEST(QueueAssign, SourceConcatItemUnknownIndexContributesX) {
  SimFixture f;
  ElaborateLowerRun(f,
                    "module t;\n"
                    "  logic [31:0] q[$] = '{10, 20, 30};\n"
                    "  logic [31:0] i;\n"
                    "  initial begin\n"
                    "    i = 32'bx;\n"
                    "    q = {q[i], 1};\n"
                    "  end\n"
                    "endmodule\n");
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_FALSE(q->elements[0].IsKnown());
  EXPECT_EQ(q->elements[1].ToUint64(), 1u);
}

TEST(QueueAssign,
     SourceConcatItemOutOfRangeIndexOnTwoStateQueueContributesZero) {
  SimFixture f;
  ElaborateLowerRun(f,
                    "module t;\n"
                    "  bit [31:0] q[$] = '{10, 20, 30};\n"
                    "  initial q = {q[5], 1};\n"
                    "endmodule\n");
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_TRUE(q->elements[0].IsKnown());
  EXPECT_EQ(q->elements[0].ToUint64(), 0u);
  EXPECT_EQ(q->elements[1].ToUint64(), 1u);
}

TEST(QueueAssign, SourceConcatItemNamingArrayGivesQueueItsOwnElementWords) {
  SimFixture f;
  auto* a0 = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a [0:1];\n"
      "  logic [7:0] q [$];\n"
      "  initial begin\n"
      "    a[0] = 8'hA5; a[1] = 8'h5A;\n"
      "    q = {a};\n"
      "  end\n"
      "endmodule\n",
      f, "a[0]");
  ASSERT_NE(a0, nullptr);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  ASSERT_NO_FATAL_FAILURE(ExpectOwnWordsCopy(a0->value, q->elements[0]));
  EXPECT_EQ(q->elements[0].words[0].aval, 0xA5u);
}

TEST(QueueAssign, ConcatOfUnsizedLiteralsThroughAHandleFillsTheProperty) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  class C;\n"
                      "    int q[$];\n"
                      "  endclass\n"
                      "  C h;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    h.q = {4, 5};\n"
                      "    out = h.q.size() * 100 + h.q[0] * 10 + h.q[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            245u);
}

TEST(QueueAssign, ConcatNamingThePropertyThroughAHandleAppendsToIt) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  class C;\n"
                      "    int q[$];\n"
                      "    function void fill();\n"
                      "      q = {7, 2, 9};\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  C h;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    h.fill();\n"
                      "    h.q = {h.q, 6};\n"
                      "    out = h.q.size() * 100 + h.q[0] * 10 + h.q[3];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            476u);
}

TEST(QueueAssign, ConcatToAStaticQueuePropertyThroughTheClassScope) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  class C;\n"
                      "    static int s[$];\n"
                      "  endclass\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C::s = {5, 15, 25};\n"
                      "    out = C::s.size() * 1000 + C::s[0] * 10 + C::s[2];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3075u);
}

}  // namespace
