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

TEST(ArrayAssignmentSimulation, DynamicArrayOfRowsCopiesEveryRow) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int d[][3], e[][3];\n"
      "  initial begin\n"
      "    d = new[2];\n"
      "    d[1][2] = 5;\n"
      "    e = d;\n"
      "    $display(\"%0d %0d %0d %0d\", e.size(), e[0].size(), e[0][0],\n"
      "             e[1][2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 3 0 5\n");
}

}  // namespace
