#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(StreamExpressionConcat, StreamingMultipleElements) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {>> {4'hA, 4'h5}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(StreamExpressionConcat, ThreeElementsLeftToRight) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [23:0] dst;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h11;\n"
      "    b = 8'h22;\n"
      "    c = 8'h33;\n"
      "    dst = {>> {a, b, c}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, UnequalWidthElementsLeftToRight) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [11:0] dst;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 4'hC;\n"
      "    dst = {>> {a, b}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCu);
}

TEST(StreamExpressionConcat, PackSingleElementPreservesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'h5A;\n"
      "    b = {>> {a}};\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

TEST(StreamExpressionConcat, NestedStreamingConcatAsElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "    dst = {>> {{>> {a}}, b}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(StreamExpressionConcat, NestedStreamingConcatBitStreamCast) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x, dst;\n"
      "  initial begin\n"
      "    x = 16'hABCD;\n"
      "    dst = {>> {{<< 8 {x}}}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDABu);
}

TEST(StreamExpressionConcat, UnpackedArrayStreamedInForeachOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [0:2];\n"
      "  logic [23:0] dst;\n"
      "  initial begin\n"
      "    arr[0] = 8'h11;\n"
      "    arr[1] = 8'h22;\n"
      "    arr[2] = 8'h33;\n"
      "    dst = {>> {arr}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, UnpackedArrayNonZeroLowBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] e [3:4];\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    e[3] = 8'hAA;\n"
      "    e[4] = 8'hBB;\n"
      "    dst = {>> {e}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBu);
}

TEST(StreamExpressionConcat, UnpackedArrayUnwrittenElementKeepsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [0:2];\n"
      "  logic [23:0] dst;\n"
      "  initial begin\n"
      "    arr[0] = 8'h11;\n"
      "    arr[2] = 8'h33;\n"
      "    dst = {>> {arr}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ((var->value.words[0].aval >> 16) & 0xFFu, 0x11u);
  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0x33u);
  EXPECT_EQ((var->value.words[0].bval >> 8) & 0xFFu, 0xFFu);
}

TEST(StreamExpressionConcat, ArrayThenScalarAppendsToRight) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] m [0:1];\n"
      "  logic [7:0] tail;\n"
      "  logic [23:0] dst;\n"
      "  initial begin\n"
      "    m[0] = 8'hAA;\n"
      "    m[1] = 8'hBB;\n"
      "    tail = 8'hCC;\n"
      "    dst = {>> {m, tail}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBCCu);
}

TEST(StreamExpressionConcat, MultiDimUnpackedArrayStreamedRowMajor) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [0:1][0:2];\n"
      "  logic [47:0] dst;\n"
      "  initial begin\n"
      "    arr[0][0] = 8'h11;\n"
      "    arr[0][1] = 8'h22;\n"
      "    arr[0][2] = 8'h33;\n"
      "    arr[1][0] = 8'h44;\n"
      "    arr[1][1] = 8'h55;\n"
      "    arr[1][2] = 8'h66;\n"
      "    dst = {>> {arr}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233445566ull);
}

TEST(StreamExpressionConcat, QueueStreamedInForeachOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte q [$] = '{8'h11, 8'h22, 8'h33};\n"
      "  logic [23:0] dst;\n"
      "  initial dst = {>> {q}};\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, DynamicArrayStreamedInForeachOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d [] = '{8'h11, 8'h22, 8'h33};\n"
      "  logic [23:0] dst;\n"
      "  initial dst = {>> {d}};\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, AssocArrayStreamedInIndexSortedOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte aa [int];\n"
      "  logic [23:0] dst;\n"
      "  initial begin\n"
      "    aa[2] = 8'h33;\n"
      "    aa[0] = 8'h11;\n"
      "    aa[1] = 8'h22;\n"
      "    dst = {>> {aa}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, AssocArrayStringKeyStreamedInKeySortedOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte aa [string];\n"
      "  logic [23:0] dst;\n"
      "  initial begin\n"
      "    aa[\"c\"] = 8'h33;\n"
      "    aa[\"a\"] = 8'h11;\n"
      "    aa[\"b\"] = 8'h22;\n"
      "    dst = {>> {aa}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, StructMembersStreamedInDeclarationOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } st;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    st.a = 8'hAB;\n"
      "    st.b = 8'hCD;\n"
      "    dst = {>> {st}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(StreamExpressionConcat, UntaggedUnionStreamsFirstMemberOnly) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    u.a = 8'hAB;\n"
      "    dst = {>> {u}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAB00u);
}

TEST(StreamExpressionConcat, NullClassHandleSkipped) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  logic [7:0] tail;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    tail = 8'hCD;\n"
      "    dst = {>> {h, tail}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCD00u);
}

TEST(StreamExpressionConcat, NonNullClassHandleStreamsBaseFirstInDeclOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class Base;\n"
      "  byte b0;\n"
      "  byte b1;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  byte d;\n"
      "endclass\n"
      "module t;\n"
      "  Derived obj;\n"
      "  logic [23:0] dst;\n"
      "  initial begin\n"
      "    obj = new;\n"
      "    obj.b0 = 8'h11;\n"
      "    obj.b1 = 8'h22;\n"
      "    obj.d = 8'h33;\n"
      "    dst = {>> {obj}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, ChildInstanceUnionStreamsFirstMemberOnly) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module M;\n"
      "  union { bit [7:0] a; bit [15:0] b; } u;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    u.a = 8'hAB;\n"
      "    dst = {>> {u}};\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f, "m.dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAB00u);
}

TEST(StreamExpressionConcat, WideStructMemberStreamsEveryWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [95:0] big; logic [7:0] low8; } s;\n"
      "  logic [103:0] dst;\n"
      "  initial begin\n"
      "    s.big = 96'h0123_4567_89AB_CDEF_0F1E_2D3C;\n"
      "    s.low8 = 8'hA5;\n"
      "    dst = {>> {s}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.width, 104u);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0xABCDEF0F1E2D3CA5u);
  EXPECT_EQ(var->value.words[1].aval, 0x0123456789u);
}

TEST(StreamExpressionConcat, WideUnionFirstMemberStreamsEveryWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  union packed { logic [95:0] w; logic [95:0] v; } u;\n"
      "  logic [95:0] dst;\n"
      "  initial begin\n"
      "    u.w = 96'hFEDC_BA98_7654_3210_0F0F_A5A5;\n"
      "    dst = {>> {u}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.width, 96u);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0x765432100F0FA5A5u);
  EXPECT_EQ(var->value.words[1].aval, 0xFEDCBA98u);
}

TEST(StreamExpressionConcat, StructMemberXBitsStreamAsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [7:0] hi; logic [7:0] lo; } s;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    s.hi = 8'b1010_xxxx;\n"
      "    s.lo = 8'h5A;\n"
      "    dst = {>> {s}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].bval & 0xFFFFu, 0x0F00u);
  EXPECT_EQ((var->value.words[0].aval >> 12) & 0xFu, 0xAu);
  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0x5Au);
}

TEST(StreamingConcatSim, AnUnpackedArrayStreamsLeftToRight) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [10:0] up [3:0]; logic [43:0] w;\n"
      "  logic [10:0] p1, p2, p3, p4;\n"
      "  initial begin\n"
      "    up[3] = 11'h123; up[2] = 11'h456; up[1] = 11'h789; up[0] = "
      "11'h0AB;\n"
      "    w = {>>{up}}; {>>{p1, p2, p3, p4}} = up;\n"
      "    $display(\"%h %h %h %h %h\", w, p1, p2, p3, p4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "24715bc48ab 123 456 789 0ab\n");
}

TEST(StreamingConcatSim, AByteQueueFromAConcatenationStreamsItsBytes) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte qb[$] = {1, 2, 3}; byte qp[$];\n"
      "  byte q12[$] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};\n"
      "  logic [23:0] w1, w2; int lh, ll, lc;\n"
      "  initial begin\n"
      "    qp = {1, 2, 3};\n"
      "    w1 = {>>{qb}}; w2 = {>>{qp}};\n"
      "    {<< byte{lh, ll, lc}} = q12;\n"
      "    $display(\"%h %h %h %h %h\", w1, w2, lh, ll, lc);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "010203 010203 0c0b0a09 08070605 04030201\n");
}

TEST(StreamingConcatSim, ClassMembersAndPackedUnionsStreamAsTheClauseSays) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class Q; byte v; endclass\n"
                 "  class B; byte b0; endclass\n"
                 "  class P extends B;\n"
                 "    int a; byte q[$]; byte d[]; byte f[2]; Q h, n;\n"
                 "  endclass\n"
                 "  P p;\n"
                 "  union soft { bit [3:0] a; bit [7:0] b; } u;\n"
                 "  bit [87:0] r;\n"
                 "  bit [7:0] ur;\n"
                 "  initial begin\n"
                 "    p = new; p.b0 = 8'h0B; p.a = 1;\n"
                 "    p.q = '{8'h11, 8'h22}; p.d = new[1]; p.d[0] = 8'h33;\n"
                 "    p.f[0] = 8'h44; p.f[1] = 8'h55;\n"
                 "    p.h = new; p.h.v = 8'h66;\n"
                 "    r = {>> {p}};\n"
                 "    u.b = 8'hA5;\n"
                 "    ur = {>> {u}};\n"
                 "    $display(\"%h %h\", r, ur);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0b00000001112233445566 a5\n");
}

}  // namespace
