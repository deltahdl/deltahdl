#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ArrayAssignmentSimulation, WholeArrayCopyEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[4];\n"
      "  int b[4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 10; a[1] = 20; a[2] = 30; a[3] = 40;\n"
      "    b = a;\n"
      "    result = b[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// §7.6: element-by-element copy applies to arrays of any element type, not just
// int. Copy a whole array of a packed-vector element type and read an element
// of the target to observe the per-element assignment for a non-int element.
TEST(ArrayAssignmentSimulation, NonIntElementWholeArrayCopy) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] a[3];\n"
      "  logic [7:0] b[3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 8'h11; a[1] = 8'h22; a[2] = 8'h33;\n"
      "    b = a;\n"
      "    result = b[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x22u);
}

TEST(ArrayAssignmentSimulation, DynamicArrayResizesOnAssign) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int dst[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    dst = src;\n"
      "    result = dst.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(ArrayAssignmentSimulation, DynamicArrayCopiesValues) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int dst[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    dst = src;\n"
      "    result = dst[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(ArrayAssignmentSimulation, LeftToRightCorrespondence) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 100; a[1] = 200; a[2] = 300;\n"
      "    b = a;\n"
      "    result = b[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 100u);
}

TEST(ArrayAssignmentSimulation, LeftToRightCorrespondenceCrossRangeDirection) {
  auto v = RunAndGet(
      "module t;\n"
      "  int A[7:0];\n"
      "  int B[1:8];\n"
      "  int result;\n"
      "  initial begin\n"
      "    B[1] = 11; B[2] = 22; B[3] = 33; B[4] = 44;\n"
      "    B[5] = 55; B[6] = 66; B[7] = 77; B[8] = 88;\n"
      "    A = B;\n"
      "    result = A[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 11u);
}

TEST(ArrayAssignmentSimulation, AssignmentPatternEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a = '{5, 10, 15};\n"
      "    result = a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 15u);
}

// §7.4.2: an unpacked dimension given as a size means the same as [0:size-1],
// so `int a[8]` declares a[0:7] and a slice of it runs from the lower index to
// the higher one. Writing it the other way round names a range the array was
// not declared with.
TEST(ArrayAssignmentSimulation, SliceLhsTreatedAsSingleAssignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[8];\n"
      "  int b[8];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 10; a[1] = 20; a[2] = 30; a[3] = 40;\n"
      "    a[4] = 50; a[5] = 60; a[6] = 70; a[7] = 80;\n"
      "    b[0:3] = a[0:3];\n"
      "    result = b[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(ArrayAssignmentSimulation, FixedSourceResizesQueueTarget) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[3];\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[0] = 100; src[1] = 200; src[2] = 300;\n"
      "    q = src;\n"
      "    result = q.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(ArrayAssignmentSimulation, FixedSourceResizesDynamicTarget) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[5];\n"
      "  int dst[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[0] = 11; src[1] = 22; src[2] = 33; src[3] = 44; src[4] = 55;\n"
      "    dst = src;\n"
      "    result = dst.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

TEST(ArrayAssignmentSimulation, DynamicSourceMatchingFixedSizeCopies) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{11, 22, 33};\n"
      "  int dst[3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    dst = src;\n"
      "    result = dst[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 22u);
}

TEST(ArrayAssignmentSimulation, QueueToFixedSizeMismatchRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int src[$];\n"
      "  int dst[2];\n"
      "  initial begin\n"
      "    dst[0] = 99;\n"
      "    dst[1] = 99;\n"
      "    src.push_back(10);\n"
      "    src.push_back(20);\n"
      "    src.push_back(30);\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array size mismatch in assignment to fixed-size array", 10, "7.6"));
}

TEST(ArrayAssignmentSimulation, DynamicToFixedSizeMismatchRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int dst[2];\n"
      "  initial begin\n"
      "    dst[0] = 99;\n"
      "    dst[1] = 99;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array size mismatch in assignment to fixed-size array", 7, "7.6"));

  auto* d0 = f.ctx.FindVariable("dst[0]");
  auto* d1 = f.ctx.FindVariable("dst[1]");
  ASSERT_NE(d0, nullptr);
  ASSERT_NE(d1, nullptr);
  EXPECT_EQ(d0->value.ToUint64(), 99u);
  EXPECT_EQ(d1->value.ToUint64(), 99u);
}

// §7.6: copying a dynamic array or queue into a fixed-size target of a
// different element count is a run-time error, and the report says §7.6 is the
// rule it enforces.
TEST(ArrayAssignmentSimulation, FixedSizeMismatchNames7_6) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int src[] = '{1, 2, 3, 4};\n"
      "  int dst[2];\n"
      "  initial dst = src;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array size mismatch in assignment to fixed-size array", 4, "7.6"));
}

// §6.8 (printed p.105): "A variable is an abstraction of a data storage
// element. A variable shall store a value from one assignment to the next."
// Each element of an unpacked array is one such storage element, so `a[0]` and
// `b[0]` are two of them, and the whole-array copy `b = a;` has to leave the
// destination element holding its own words rather than the pointer to the
// source's that a plain Logic4Vec assignment copies (types.h: the struct holds
// Logic4Word* words, and assigning it copies the pointer).
//
// The claim is made on the storage identity rather than on a value read back
// from SystemVerilog because no source-level reader can currently tell the two
// apart: every writer that reaches an unpacked-array element replaces the
// element's vector instead of depositing into it. WriteVar installs the fresh
// value ResizeToWidth builds, WritePartSelect rebuilds the element with
// ExtractBitField, and the one in-place depositor -- WriteResolvedField's
// kBits arm -- is not reachable through a select, because BuildLhsName spells
// a kSelect node as "". Add a writer that deposits into an unpacked-array
// element in place, or a store on this path that coerces rather than replaces
// (CoerceTo2State writes through whatever words it is handed), and the sharing
// becomes visible from source as a write to `b[0]` that changes `a[0]`. Until
// one of those exists the pointer is the only place this rule can be observed,
// so the pointer assertion is the test rather than scaffolding around one.
TEST(ArrayAssignmentSimulation,
     WholeArrayCopyGivesDestinationItsOwnElementWords) {
  SimFixture f;
  auto* a0 = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a [0:1];\n"
      "  logic [7:0] b [0:1];\n"
      "  initial begin\n"
      "    a[0] = 8'hA5; a[1] = 8'h5A;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f, "a[0]");
  ASSERT_NE(a0, nullptr);
  auto* b0 = f.ctx.FindVariable("b[0]");
  ASSERT_NE(b0, nullptr);
  ASSERT_NO_FATAL_FAILURE(ExpectOwnWordsCopy(a0->value, b0->value));
}

// The same §6.8 storage rule on the other arm of the copy: a queue source runs
// through CopyResizableSourceToArray rather than CopyArrayElements, and a queue
// entry outlives the statement that read it, so `a[0]` must not end up pointing
// at the words `q[0]` still holds. This asserts on the pointer for the reason
// the array-to-array case above spells out -- WriteVar, WritePartSelect and
// WriteResolvedField all replace an unpacked-array element rather than deposit
// into it, so shared words are invisible to any SystemVerilog reader until a
// writer deposits in place or a store on this path coerces instead of
// replacing.
TEST(ArrayAssignmentSimulation,
     WholeArrayCopyFromQueueGivesDestinationItsOwnElementWords) {
  SimFixture f;
  auto* a0 = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  int a [0:1];\n"
      "  initial begin\n"
      "    q.push_back(32'h1234_5678);\n"
      "    q.push_back(32'h0BAD_F00D);\n"
      "    a = q;\n"
      "  end\n"
      "endmodule\n",
      f, "a[0]");
  ASSERT_NE(a0, nullptr);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  ASSERT_NO_FATAL_FAILURE(ExpectOwnWordsCopy(a0->value, q->elements[0]));
}

// §6.22.2's example run: `C = A` copies A's elements left to right into C's,
// so A[0] lands in C[6], and `A = C` copies them back, C[6] into A[0].
TEST(ArrayAssignmentSimulation, TypedefElementArrayCopiesBothWays) {
  const char* src =
      "module t;\n"
      "  typedef bit [10:1] uint10;\n"
      "  bit [9:0] A [0:5];\n"
      "  uint10 C [6:1];\n"
      "  int c6, a0;\n"
      "  initial begin\n"
      "    A[0] = 5;\n"
      "    C = A;\n"
      "    c6 = C[6];\n"
      "    C[6] = 9;\n"
      "    A = C;\n"
      "    a0 = A[0];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "c6"), 5u);
  EXPECT_EQ(RunAndGet(src, "a0"), 9u);
}

// §7.6 with §8.5: a fixed array property assigned from another object's
// property of the same shape takes every element, and the two stay
// independent: a later write to one leaves the other as copied.
TEST(ArrayAssignmentSimulation, FixedArrayPropertyCopiedBetweenObjects) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C; int arr[4]; endclass\n"
      "  C g, h;\n"
      "  initial begin\n"
      "    g = new; h = new;\n"
      "    h.arr[0] = 10; h.arr[1] = 20; h.arr[2] = 30; h.arr[3] = 40;\n"
      "    g.arr = h.arr;\n"
      "    h.arr[1] = 77;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", g.arr[0], g.arr[1], g.arr[2],\n"
      "             g.arr[3], h.arr[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "10 20 30 40 77\n");
}

// §7.6 with §7.5, §7.10 and §8.5: a queue property assigned to a dynamic array
// property gives it the queue's size and elements, and the dynamic array
// assigned back to the emptied queue refills it, inside a method as through
// handles.
TEST(ArrayAssignmentSimulation, QueueAndDynamicArrayPropertiesAssignedAcross) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Q; int q[$]; endclass\n"
      "  class D; int d[]; int e[];\n"
      "    function void keep(); e = d; endfunction\n"
      "  endclass\n"
      "  Q a; D b;\n"
      "  initial begin\n"
      "    a = new; b = new;\n"
      "    a.q.push_back(10); a.q.push_back(20); a.q.push_back(30);\n"
      "    b.d = a.q; b.keep();\n"
      "    a.q.delete();\n"
      "    a.q = b.e;\n"
      "    $display(\"%0d %0d %0d %0d\", b.d.size(), b.d[1], a.q.size(),\n"
      "             a.q[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 20 3 30\n");
}

// §7.6 with §7.4.2: whole assignment and equality of multidimensional
// fixed-size arrays of one shape take every element, a two- and a three-
// dimensional array alike, and an unequal element makes the arrays unequal.
TEST(ArrayAssignmentSimulation, MultidimensionalArraysCopiedAndComparedWhole) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int a2[2][3], b2[2][3];\n"
      "  int a3[2][3][4], b3[2][3][4];\n"
      "  initial begin\n"
      "    b2[1][2] = 21; b3[1][2][3] = 123; b3[0][0][1] = 4;\n"
      "    a2 = b2; a3 = b3;\n"
      "    $display(\"%0d %0d %0d %0d\", a2[1][2], a3[1][2][3], a2 == b2,\n"
      "             a3 == b3);\n"
      "    a3[0][0][1] = 5;\n"
      "    $display(\"%0d %0d\", a3 == b3, a3 != b3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "21 123 1 1\n0 1\n");
}

// §7.4.4 with §7.6: a select omitting the fastest-varying indices names a
// subarray, assigned from another subarray or a one-dimensional array of its
// size and read into one, each by position.
TEST(ArrayAssignmentSimulation, SubarraysAssignedByPosition) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int A[2][3][4], B[2][3][4], C[5][4], R[4];\n"
      "  initial begin\n"
      "    foreach (B[i,j,k]) B[i][j][k] = i*100 + j*10 + k;\n"
      "    foreach (C[i,j]) C[i][j] = 6 + j;\n"
      "    A[0][2] = C[0];\n"
      "    A[1] = B[0];\n"
      "    R = B[1][2];\n"
      "    $display(\"%0d %0d %0d %0d %0d\", A[0][2][0], A[0][2][3],\n"
      "             A[1][1][3], A[1][2][3], R[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "6 9 13 23 123\n");
}

// §7.6: a dynamic array assigned to a fixed-size subarray pairs left to
// right, so B[0] reaches the left end of a `[100:1]` row, index 100; a
// dynamic array of another size is a run-time error and writes nothing.
TEST(ArrayAssignmentSimulation, DynamicArrayToAFixedSubarray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[2][100:1];\n"
      "  int B[] = new[100];\n"
      "  int C[] = new[8];\n"
      "  initial begin\n"
      "    B[0] = 7; B[99] = 100;\n"
      "    A[1] = B;\n"
      "    A[0][3] = 42;\n"
      "    A[0] = C;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array size mismatch in assignment to fixed-size array", 9, "7.6"));
  auto* left = f.ctx.FindVariable("A[1][100]");
  auto* right = f.ctx.FindVariable("A[1][1]");
  auto* kept = f.ctx.FindVariable("A[0][3]");
  ASSERT_NE(left, nullptr);
  ASSERT_NE(right, nullptr);
  ASSERT_NE(kept, nullptr);
  EXPECT_EQ(left->value.ToUint64(), 7u);
  EXPECT_EQ(right->value.ToUint64(), 100u);
  EXPECT_EQ(kept->value.ToUint64(), 42u);
}

}  // namespace
