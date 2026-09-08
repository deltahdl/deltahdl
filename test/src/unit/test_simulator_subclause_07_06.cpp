#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

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
  ASSERT_NE(a0->value.words, nullptr);
  ASSERT_NE(b0->value.words, nullptr);
  EXPECT_NE(a0->value.words, b0->value.words);
  EXPECT_EQ(a0->value.words[0].aval, b0->value.words[0].aval);
  EXPECT_EQ(a0->value.words[0].bval, b0->value.words[0].bval);
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
  ASSERT_NE(a0->value.words, nullptr);
  ASSERT_NE(q->elements[0].words, nullptr);
  EXPECT_NE(a0->value.words, q->elements[0].words);
  EXPECT_EQ(a0->value.words[0].aval, q->elements[0].words[0].aval);
  EXPECT_EQ(a0->value.words[0].bval, q->elements[0].words[0].bval);
}

}  // namespace
