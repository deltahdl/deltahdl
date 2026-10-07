#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
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

}  // namespace
