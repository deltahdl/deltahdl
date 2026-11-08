#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DeclarationRangeSim, UnsizedDimensionYieldsDynamicArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[] = '{2, 4, 6, 8};\n"
      "  int result;\n"
      "  initial result = a.sum();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DeclarationRangeSim, UnpackedSizeLiteralYieldsFixedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[4] = '{1, 2, 3, 4};\n"
      "  int result;\n"
      "  initial result = a.sum();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

TEST(DeclarationRangeSim, UnpackedSizeParameterYieldsFixedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 4;\n"
      "  int a[P] = '{1, 2, 3, 4};\n"
      "  int result;\n"
      "  initial result = a.sum();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

TEST(DeclarationRangeSim, UnpackedRangeYieldsFixedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[1:3] = '{10, 20, 30};\n"
      "  int result;\n"
      "  initial result = a.sum();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

TEST(DeclarationRangeSim, PackedRangeLiteralAppliesWidth) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] vec;\n"
      "  int result;\n"
      "  initial begin\n"
      "    vec = 8'hFF;\n"
      "    vec = vec + 8'd1;\n"
      "    result = vec;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DeclarationRangeSim, PackedRangeParameterAppliesWidth) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int W = 8;\n"
      "  logic [W-1:0] vec;\n"
      "  int result;\n"
      "  initial begin\n"
      "    vec = 8'hFF;\n"
      "    vec = vec + 8'd1;\n"
      "    result = vec;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DeclarationRangeSim, AssociativeIntegerIndexYieldsAssocArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 55;\n"
      "    result = aa[10];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 55u);
}

TEST(DeclarationRangeSim, AssociativeStringIndexYieldsAssocArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"k\"] = 33;\n"
      "    result = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 33u);
}

TEST(DeclarationRangeSim, AssociativeWildcardYieldsAssocArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 77;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

TEST(DeclarationRangeSim, QueueUnboundedYieldsQueue) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(2);\n"
      "    q.push_back(3);\n"
      "    result = q.size;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(DeclarationRangeSim, QueueBoundedLiteralYieldsQueue) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$:7];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(2);\n"
      "    q.push_back(3);\n"
      "    result = q.size;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(DeclarationRangeSim, QueueBoundedParameterYieldsQueue) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int B = 7;\n"
      "  int q[$:B];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(2);\n"
      "    q.push_back(3);\n"
      "    result = q.size;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(DeclarationRangeSim, DataTypeIndexFormsInBlockAreAssociative) {
  auto v = RunAndGet(
      "class P #(int N = 1); endclass\n"
      "module t;\n"
      "  bit [3:0] k;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int e [enum {A, B}];\n"
      "    int s [struct packed {bit [3:0] v;}];\n"
      "    int y [type(k)];\n"
      "    int z [type(string)];\n"
      "    int c [P#(8)];\n"
      "    P#(8) h;\n"
      "    h = new;\n"
      "    e[1] = 5;\n"
      "    s[3] = 6;\n"
      "    y[17] = 7;\n"
      "    z[\"abcde\"] = 1;\n"
      "    z[\"bcde\"] = 1;\n"
      "    c[h] = 9;\n"
      "    result = e.num() * 100000 + e[1] * 10000 + s[3] * 1000 +\n"
      "             y[1] * 100 + z.num() * 10 + c[h];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 156729u);
}

TEST(DeclarationRangeSim, StructureIndexInFunctionBodyIsAssociative) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function automatic int count();\n"
      "    int a [struct packed {bit [3:0] v;}];\n"
      "    a[19] = 4;\n"
      "    return a.num() * 10 + a[3];\n"
      "  endfunction\n"
      "  initial result = count();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 14u);
}

TEST(DeclarationRangeSim, TypeRefIndexOfClassPropertyIsAssociative) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] k;\n"
      "  int result;\n"
      "  class C;\n"
      "    int m [type(k)];\n"
      "  endclass\n"
      "  initial begin\n"
      "    C o;\n"
      "    o = new;\n"
      "    o.m[18] = 3;\n"
      "    result = o.m.num() * 10 + o.m[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 13u);
}

TEST(DeclarationRangeSim, StructureIndexOfPackageVariableIsAssociative) {
  auto v = RunAndGet(
      "package q;\n"
      "  int a [struct packed {bit [3:0] v;}];\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    q::a[20] = 6;\n"
      "    result = q::a.num() * 10 + q::a[4];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 16u);
}

TEST(DeclarationRangeSim, ScopedTypedefIndexInBlockIsAssociative) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef bit [3:0] idx_t;\n"
      "  parameter int N = 4;\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a [p::idx_t];\n"
      "    int f [p::N];\n"
      "    a[17] = 5;\n"
      "    result = a.num() * 100 + a[1] * 10 + $size(f);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 154u);
}

TEST(DeclarationRangeSim, ScopedTypedefIndexInSubroutineAndClassIsAssociative) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef bit [3:0] idx_t;\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  class C;\n"
      "    int m [p::idx_t];\n"
      "  endclass\n"
      "  function automatic int count();\n"
      "    int a [p::idx_t];\n"
      "    a[19] = 4;\n"
      "    return a.num() * 10 + a[3];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    C o;\n"
      "    o = new;\n"
      "    o.m[18] = 3;\n"
      "    result = count() * 100 + o.m.num() * 10 + o.m[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1413u);
}

TEST(DeclarationRangeSim, ScopedTypedefIndexOfPackageVariableIsAssociative) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef bit [3:0] idx_t;\n"
      "endpackage\n"
      "package q;\n"
      "  int a [p::idx_t];\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    q::a[20] = 6;\n"
      "    result = q::a.num() * 10 + q::a[4];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 16u);
}

TEST(DeclarationRangeSim, NestedClassScopedIndexKeysByHandle) {
  auto v = RunAndGet(
      "class Outer;\n"
      "  class Inner; endclass\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a [Outer::Inner];\n"
      "    Outer::Inner h1, h2;\n"
      "    h1 = new;\n"
      "    h2 = new;\n"
      "    a[h1] = 8;\n"
      "    a[h2] = 9;\n"
      "    result = a.num() * 10 + a[h2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 29u);
}

}  // namespace
