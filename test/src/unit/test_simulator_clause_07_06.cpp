#include "fixture_simulator.h"
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

TEST(ArrayAssignmentSimulation, SliceLhsTreatedAsSingleAssignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[8];\n"
      "  int b[8];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 10; a[1] = 20; a[2] = 30; a[3] = 40;\n"
      "    a[4] = 50; a[5] = 60; a[6] = 70; a[7] = 80;\n"
      "    b[3:0] = a[3:0];\n"
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());

  auto* d0 = f.ctx.FindVariable("dst[0]");
  auto* d1 = f.ctx.FindVariable("dst[1]");
  ASSERT_NE(d0, nullptr);
  ASSERT_NE(d1, nullptr);
  EXPECT_EQ(d0->value.ToUint64(), 99u);
  EXPECT_EQ(d1->value.ToUint64(), 99u);
}

}  // namespace
