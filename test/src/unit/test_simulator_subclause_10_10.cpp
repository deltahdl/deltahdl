#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

Expr* MakeConcat(Arena& arena, std::vector<Expr*> elems) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kConcatenation;
  e->elements = std::move(elems);
  return e;
}

TEST(UnpackedArrayConcatSim, LeftToRightArrangement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[1:3];\n"
      "  initial A = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a1 = f.ctx.FindVariable("A[1]");
  auto* a2 = f.ctx.FindVariable("A[2]");
  auto* a3 = f.ctx.FindVariable("A[3]");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  ASSERT_NE(a3, nullptr);
  EXPECT_EQ(a1->value.ToUint64(), 10u);
  EXPECT_EQ(a2->value.ToUint64(), 20u);
  EXPECT_EQ(a3->value.ToUint64(), 30u);
}

TEST(UnpackedArrayConcatSim, EmptyConcatClearsQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  initial q = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->elements.empty());
}

TEST(UnpackedArrayConcatSim, ConcatToQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

// An item whose self-determined type is an unpacked array of the target's
// element type contributes its members, preserving their internal left-to-
// right order. Joining two such items shall give a queue with the first
// item's members followed by the second item's members.
TEST(UnpackedArrayConcatSim, ConcatWithArrayItemsExpandsLeftToRight) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[0:1] = '{10, 20};\n"
      "  int B[0:1] = '{30, 40};\n"
      "  int q[$];\n"
      "  initial q = {A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 40u);
}

// §10.10: an array item stands for all of its elements, in the left-to-right
// order it holds them. Left to right is the order the declaration writes, so
// `int A[1:0]` contributes A[1] first. Each element is written through its own
// subscript rather than through an assignment pattern, so that the order the
// pattern would fill the array in cannot cancel the order the concatenation
// expands it in and leave the same answer either way.
TEST(UnpackedArrayConcatSim, DescendingArrayItemExpandsHighestIndexFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[1:0];\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    A[1] = 10;\n"
      "    A[0] = 20;\n"
      "    q = {A};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(UnpackedArrayConcatSim, ConcatToDynamicArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  initial d = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("d");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(UnpackedArrayConcatSim, EmptyConcatToFixedSizeError) {
  SimFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_descending = false;
  f.ctx.RegisterArray("A", info);
  for (uint32_t i = 0; i < 3; ++i)
    f.ctx.CreateVariable("A[" + std::to_string(i) + "]", 32);
  auto* rhs = MakeConcat(f.arena, {});
  auto* stmt = MakeAssign(f.arena, "A", rhs);
  TryArrayBlockingAssign(stmt, f.ctx, f.arena);
  // The concatenation is built in the arena rather than parsed, so the report
  // carries the default location of line 0.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch: "
                            "expected 3 elements, got 0",
                            0, "10.10"));
}

// §10.10: a resulting array whose size differs from a fixed-size target's
// element count is an error. The size-mismatch rule is a runtime rule that
// fires only when the fixed-size target and the concatenation meet in a
// procedural assignment, so it must be driven from real source (a declaration +
// an initial-block assignment) rather than from a hand-built ArrayInfo.
// Elaboration stays clean; the error appears when the assignment runs.
TEST(UnpackedArrayConcatSim, FixedSizeMismatchFromSourceErrorsAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3, 4};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch: "
                            "expected 3 elements, got 4",
                            3, "10.10"));
}

// §10.10: when the size exceeds a bounded queue's maximum, the elements past
// the target's upper bound are dropped with a warning. The bound comes from the
// queue_dimension of §7.10 (`[$:1]` → capacity 2), so this weaves §7.10's
// bounded-queue target with §10.10's overflow rule and is driven end to end
// from source: the third item is dropped and a warning is raised, leaving
// exactly two elements.
TEST(UnpackedArrayConcatSim, BoundedQueueOverflowFromSourceTruncatesAndWarns) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$:1];\n"
      "  initial q = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto warnings_before = f.diag.WarningCount();
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_GT(f.diag.WarningCount(), warnings_before);
}

// §10.10: it shall be an error if the size of the array an unpacked array
// concatenation forms differs from the element count of a fixed-size target.
// The report a blocking assignment raises names §10.10.
TEST(UnpackedArrayConcatSim, BlockingSizeMismatchNames10_10) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[2];\n"
      "  initial A = {5, 6, 7};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch", 3,
                            "10.10"));
}

// §10.10: a nonblocking assignment applies the concatenation on its own update
// path and reaches the same rule, so its report names the same subclause.
TEST(UnpackedArrayConcatSim, NonblockingSizeMismatchNames10_10) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int B[2];\n"
      "  initial B <= {8, 9, 10};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch", 3,
                            "10.10"));
}

// §10.10: an item naming an unpacked array stands for all of its elements, in
// the left-to-right order it holds them, so `b = {a}` hands the two elements of
// `a` to the two elements of `b`, in that order. Each of those four names is a
// variable in its own right, so the concatenation has to leave `b[0]` holding
// its own words; ExpectOwnWordsCopy is where that claim and the reasoning
// behind the pointer comparison live.
//
// The widths match here, which is the case that hides the bug: the collector
// pushes the source variable's own vector and the resize on the store returns
// it untouched, so nothing on the path allocates and the two elements end up
// sharing a buffer. The claim is made on the storage identity, as it is for
// the whole-array copy of §7.6, because no source-level reader can currently
// tell the two apart: every writer that reaches an unpacked-array element
// replaces the element's vector instead of depositing into it. The literal
// read back from `b[0]` alongside it says the concatenation really did deliver
// `a[0]`'s value rather than quietly doing nothing.
TEST(UnpackedArrayConcatSim, ArrayItemGivesDestinationItsOwnElementWords) {
  SimFixture f;
  auto* a0 = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a [0:1];\n"
      "  logic [7:0] b [0:1];\n"
      "  initial begin\n"
      "    a[0] = 8'hA5; a[1] = 8'h5A;\n"
      "    b = {a};\n"
      "  end\n"
      "endmodule\n",
      f, "a[0]");
  ASSERT_NE(a0, nullptr);
  auto* b0 = f.ctx.FindVariable("b[0]");
  ASSERT_NE(b0, nullptr);
  ASSERT_NO_FATAL_FAILURE(ExpectOwnWordsCopy(a0->value, b0->value));
  EXPECT_EQ(b0->value.words[0].aval, 0xA5u);
}

// §10.10 (printed page 264): braces assigned to a target of an unpacked array
// type are an unpacked array concatenation, and §7.4 with §7.10 (printed pages
// 153 and 169) makes an element selected from an array whose elements are
// queues a queue itself -- a fixed-size array of a queue typedef, an
// associative array of one and a queue of queues alike. The elaborator took
// the braces for a vector concatenation, whose unsized items §11.4.12 bars, and
// reported each of 1, 2 and 5; the run then wrote the element's own queue
// nothing. `{qq[0], 5}` reads the element's queue as an item, contributing its
// elements.
TEST(UnpackedArrayConcatSim, BracesAssignedToAQueueElementFillItsQueue) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef int q_t[$];\n"
      "  q_t fx[2];\n"
      "  q_t aa[string];\n"
      "  int qq[$][$];\n"
      "  initial begin\n"
      "    fx[0] = {1, 2};\n"
      "    aa[\"k\"] = {5};\n"
      "    qq.push_back({});\n"
      "    qq[0] = {qq[0], 5};\n"
      "    qq[0] = {qq[0], 6};\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", fx[0].size(), fx[0][1],\n"
      "             aa[\"k\"].size(), aa[\"k\"][0], qq[0].size(), qq[0][0],\n"
      "             qq[0][1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2 1 5 2 5 6\n");
}

// §10.10 with §7.4 and §7.10: assigned to a queue whose elements are arrays,
// an item of that element type is one element of the concatenation, where an
// item that is an array of the element type contributes each of its elements.
// `a`, an `int [3]`, is one row of `int r[$][3]`, as the selected row `r[0]`
// is, and `b`, an `int [$]`, one element of `int s[$][$]`; `r` itself
// contributes its rows as they stood before the assignment.
TEST(UnpackedArrayConcatSim, ItemOfTheQueuesElementTypeIsOneElement) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int r[$][3];\n"
      "  int a[3] = '{1, 2, 3};\n"
      "  int s[$][$];\n"
      "  int b[$] = '{7, 8};\n"
      "  initial begin\n"
      "    r.push_back('{4, 5, 6});\n"
      "    r = {r, a};\n"
      "    r = {r, r[0]};\n"
      "    s = {b, b};\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", r.size(), r[0][2],\n"
      "             r[1][0], r[1][2], r[2][1], s.size(), s[1][1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 6 1 3 5 2 8\n");
}

// §10.10: each item of an unpacked array concatenation is an expression whose
// value becomes its element, so an item with a side effect has it once. The
// right-hand side was evaluated whole as a vector before being distributed,
// and each call ran twice.
TEST(UnpackedArrayConcatSim, EachItemIsEvaluatedOnce) {
  const char* src =
      "module t;\n"
      "  int n = 0;\n"
      "  int A[2];\n"
      "  int a0, a1, calls;\n"
      "  function int f(); n++; return n; endfunction\n"
      "  initial begin A = {f(), f()}; a0 = A[0]; a1 = A[1]; calls = n; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a0"), 1u);
  EXPECT_EQ(RunAndGet(src, "a1"), 2u);
  EXPECT_EQ(RunAndGet(src, "calls"), 2u);
}

// §10.10: a slice of an unpacked array is an item whose type is an unpacked
// array, so it contributes each of its elements, while an element select
// beside it is one element. The slice was evaluated as one value and the
// assignment reported a size mismatch.
TEST(UnpackedArrayConcatSim, ASliceItemContributesItsElements) {
  const char* src =
      "module t;\n"
      "  int A[4] = '{1, 2, 3, 4};\n"
      "  int B[3];\n"
      "  int b0, b1, b2;\n"
      "  initial begin B = {A[1:2], A[0]}; b0 = B[0]; b1 = B[1]; b2 = B[2]; "
      "end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "b0"), 2u);
  EXPECT_EQ(RunAndGet(src, "b1"), 3u);
  EXPECT_EQ(RunAndGet(src, "b2"), 1u);
}

// §10.10: an item whose type is the target's element type is one element, so
// each row of a two-dimensional array takes one whole array item. Each item
// was counted by its own elements, giving six for a target of two.
TEST(UnpackedArrayConcatSim, AnItemOfTheElementTypeIsOneRow) {
  const char* src =
      "module t;\n"
      "  int M[2][3];\n"
      "  int R[3] = '{1, 2, 3};\n"
      "  int S[3] = '{4, 5, 6};\n"
      "  int m02, m10;\n"
      "  initial begin M = {R, S}; m02 = M[0][2]; m10 = M[1][0]; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "m02"), 3u);
  EXPECT_EQ(RunAndGet(src, "m10"), 4u);
}

// §10.10: a typed pattern item whose type is the target's structure element
// type is one element; only one of an unpacked array type contributes each of
// its elements. Every typed pattern was expanded, so two structure items
// counted four.
TEST(UnpackedArrayConcatSim, ATypedStructurePatternItemIsOneElement) {
  const char* src =
      "typedef struct packed { byte a, b; } P;\n"
      "module t;\n"
      "  P arr[2];\n"
      "  int e0, e1;\n"
      "  initial begin\n"
      "    arr = {P'{8'h1, 8'h2}, P'{8'h3, 8'h4}};\n"
      "    e0 = arr[0]; e1 = arr[1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "e0"), 0x0102u);
  EXPECT_EQ(RunAndGet(src, "e1"), 0x0304u);
}

// §10.10.1: a typed pattern item of an unpacked array type, `AI3'{2, 3, 4}`,
// still contributes each of its elements to a fixed-size target.
TEST(UnpackedArrayConcatSim, ATypedArrayPatternItemFillsSeveralElements) {
  const char* src =
      "module t;\n"
      "  typedef int AI3[1:3];\n"
      "  int A5[1:5];\n"
      "  int a2, a4, a5;\n"
      "  initial begin\n"
      "    A5 = {1, AI3'{2, 3, 4}, 5};\n"
      "    a2 = A5[2]; a4 = A5[4]; a5 = A5[5];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a2"), 2u);
  EXPECT_EQ(RunAndGet(src, "a4"), 4u);
  EXPECT_EQ(RunAndGet(src, "a5"), 5u);
}

// §10.10.1 with §10.4.2: a nonblocking assignment collects the items of an
// unpacked array concatenation as the blocking one does, so a typed pattern
// of an unpacked array type contributes each of its elements. It counted as
// one, and the assignment reported 7 elements for 9.
TEST(UnpackedArrayConcatSim, ANonblockingConcatenationExpandsATypedArrayItem) {
  const char* src =
      "module t;\n"
      "  typedef int AI3[1:3];\n"
      "  int A3[1:3] = '{1, 2, 3};\n"
      "  int A9[1:9];\n"
      "  int a5, a9;\n"
      "  initial begin\n"
      "    A9 <= {A3, 4, AI3'{5, 6, 7}, 8, 9};\n"
      "    #1 a5 = A9[5]; a9 = A9[9];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a5"), 5u);
  EXPECT_EQ(RunAndGet(src, "a9"), 9u);
}

// §10.10: a dynamic array is a legal target, the concatenation giving it its
// size, by a nonblocking assignment as by a blocking one. The nonblocking
// assignment compared three elements against a size of 0 and wrote none.
TEST(UnpackedArrayConcatSim, ANonblockingConcatenationSizesADynamicArray) {
  const char* src =
      "module t;\n"
      "  int d[];\n"
      "  int n, d2;\n"
      "  initial begin d <= {1, 2, 3}; #1 n = d.size(); d2 = d[2]; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 3u);
  EXPECT_EQ(RunAndGet(src, "d2"), 3u);
}

// §10.10: a declaration's initializer that is an unpacked array concatenation
// expands an array item into its elements, into a fixed-size array and into a
// queue alike. Each item filled one element, so B[0] took A as one value.
TEST(UnpackedArrayConcatSim, ADeclarationInitializerExpandsAnArrayItem) {
  const char* src =
      "module t;\n"
      "  int A[2] = '{10, 20};\n"
      "  int B[4] = {A, 30, 40};\n"
      "  int q[$] = {A, 5};\n"
      "  int b0, b1, b3, n, q1;\n"
      "  initial begin b0 = B[0]; b1 = B[1]; b3 = B[3]; n = q.size(); q1 = "
      "q[1]; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "b0"), 10u);
  EXPECT_EQ(RunAndGet(src, "b1"), 20u);
  EXPECT_EQ(RunAndGet(src, "b3"), 40u);
  EXPECT_EQ(RunAndGet(src, "n"), 3u);
  EXPECT_EQ(RunAndGet(src, "q1"), 20u);
}

// §10.10: a concatenation giving a fixed-size array a different number of
// elements is an error in a declaration's initializer as in an assignment.
TEST(UnpackedArrayConcatSim, ADeclarationInitializerOfTheWrongSizeIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int C[3] = {1, 2};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch: "
                            "expected 3 elements, got 2",
                            2, "10.10"));
}

// §10.10.3: an item of a multidimensional assignment pattern that is written
// in braces is an unpacked array concatenation over its row, so an array item
// in it contributes each of its elements. It was read as a nested positional
// pattern, A standing as one value and C[0][1] left at 0.
TEST(UnpackedArrayConcatSim, ABracedPatternItemIsAConcatenationOverItsRow) {
  const char* src =
      "module t;\n"
      "  int A[2] = '{1, 2};\n"
      "  int C[2][2];\n"
      "  int c00, c01, c10, c11;\n"
      "  initial begin\n"
      "    C = '{{A}, {3, 4}};\n"
      "    c00 = C[0][0]; c01 = C[0][1]; c10 = C[1][0]; c11 = C[1][1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "c00"), 1u);
  EXPECT_EQ(RunAndGet(src, "c01"), 2u);
  EXPECT_EQ(RunAndGet(src, "c10"), 3u);
  EXPECT_EQ(RunAndGet(src, "c11"), 4u);
}

// §10.10: a row's concatenation of the wrong size is reported as any
// concatenation's is.
TEST(UnpackedArrayConcatSim, ABracedPatternItemOfTheWrongSizeIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int C[2][2];\n"
      "  initial C = '{{1}, {3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch: "
                            "expected 2 elements, got 1",
                            3, "10.10"));
}

}  // namespace
