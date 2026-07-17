#include "fixture_simulator.h"

using namespace delta;

namespace {

// §11.4.14.1 packs each stream_expression, left to right, onto the right end of
// the generic stream. Every test below drives a real streaming concatenation
// through the full pipeline (parse, elaborate, lower, run) and reads the packed
// result from a language-level variable, so it observes the production pack
// procedure (eval_streaming.cpp) rather than a hand-assembled intermediate.

TEST(StreamExpressionConcat, StreamingMultipleElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {>> {4'hA, 4'h5}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(StreamExpressionConcat, ThreeElementsLeftToRight) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, UnequalWidthElementsLeftToRight) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCu);
}

TEST(StreamExpressionConcat, PackSingleElementPreservesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'h5A;\n"
      "    b = {>> {a}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

// §11.4.14.1: an operand that is itself a streaming_concatenation is cast to a
// packed array of bit and appended to the right end of the generic stream. The
// inner {>> {a}} contributes a's 8 bits ahead of b, so a lands at the most
// significant end.
TEST(StreamExpressionConcat, NestedStreamingConcatAsElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "    dst = {>> {{>> {a}}, b}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

// §11.4.14.1: the bit-stream produced by an inner streaming_concatenation is
// appended as-is. The inner {<< 8 {x}} reverses x's two bytes (0xABCD ->
// 0xCDAB), and the outer >> concatenation then packs that byte-swapped stream
// unchanged.
TEST(StreamExpressionConcat, NestedStreamingConcatBitStreamCast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x, dst;\n"
      "  initial begin\n"
      "    x = 16'hABCD;\n"
      "    dst = {>> {{<< 8 {x}}}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDABu);
}

// §11.4.14.1: an unpacked array operand is expanded by applying the procedure
// to each element in foreach-traversal order (§12.7.3), i.e. ascending index.
// arr[0] streams first and lands at the most significant end; any other order
// would change the packed value.
TEST(StreamExpressionConcat, UnpackedArrayStreamedInForeachOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

// §11.4.14.1: foreach traversal starts at the array's declared low bound, not
// at zero. For arr[3:4] the element at index 3 streams first.
TEST(StreamExpressionConcat, UnpackedArrayNonZeroLowBound) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] e [3:4];\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    e[3] = 8'hAA;\n"
      "    e[4] = 8'hBB;\n"
      "    dst = {>> {e}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBu);
}

// §11.4.14.1: because the procedure is applied element by element, an unwritten
// 4-state element contributes its own x bits to the stream rather than being
// merged away. arr[1] is never assigned, so the middle byte of the packed
// stream is unknown while the assigned bytes survive around it.
TEST(StreamExpressionConcat, UnpackedArrayUnwrittenElementKeepsX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:2];\n"
      "  logic [23:0] dst;\n"
      "  initial begin\n"
      "    arr[0] = 8'h11;\n"
      "    arr[2] = 8'h33;\n"
      "    dst = {>> {arr}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  // The assigned elements keep their known values on either side of the
  // unknown middle byte, which is fully x.
  EXPECT_EQ((var->value.words[0].aval >> 16) & 0xFFu, 0x11u);
  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0x33u);
  EXPECT_EQ((var->value.words[0].bval >> 8) & 0xFFu, 0xFFu);
}

// §11.4.14.1: an aggregate operand is expanded in place and a following scalar
// is appended to the right of the expanded elements. arr[0], arr[1] occupy the
// high bytes and the trailing scalar lands at the least significant end.
TEST(StreamExpressionConcat, ArrayThenScalarAppendsToRight) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBCCu);
}

// §11.4.14.1: a multidimensional fixed unpacked array is still one unpacked
// array, streamed in the order a foreach with a single index variable traverses
// it -- row-major, outermost dimension first. Element [0][0] streams first
// (most significant end) and [1][2] last; any other traversal would reorder the
// bytes.
TEST(StreamExpressionConcat, MultiDimUnpackedArrayStreamedRowMajor) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233445566ull);
}

// §11.4.14.1: a queue is an unpacked array, so the procedure is applied to each
// element in foreach-traversal order (ascending index). The element at index 0
// lands at the most significant end of the generic stream.
TEST(StreamExpressionConcat, QueueStreamedInForeachOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q [$] = '{8'h11, 8'h22, 8'h33};\n"
      "  logic [23:0] dst;\n"
      "  initial dst = {>> {q}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

// §11.4.14.1: a dynamic array is one of the unpacked-array forms streamed
// element by element in foreach-traversal order. Its live elements are held in
// the backing store rather than in per-index leaf variables, so this exercises
// the branch that packs from that store; the element at index 0 lands at the
// most significant end.
TEST(StreamExpressionConcat, DynamicArrayStreamedInForeachOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] d [] = '{8'h11, 8'h22, 8'h33};\n"
      "  logic [23:0] dst;\n"
      "  initial dst = {>> {d}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

// §11.4.14.1: an associative array is streamed in index-sorted order. Entries
// are written out of key order to prove the stream follows ascending index, not
// insertion order: key 0 lands at the most significant end.
TEST(StreamExpressionConcat, AssocArrayStreamedInIndexSortedOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

// §11.4.14.1: index-sorted order applies to a string-keyed associative array
// too, where the ordering is lexicographic over the keys. Entries are written
// out of key order to prove the stream follows sorted key order, not insertion
// order: key "a" streams first and lands at the most significant end.
TEST(StreamExpressionConcat, AssocArrayStringKeyStreamedInKeySortedOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

// §11.4.14.1: a struct is streamed by applying the procedure to each member in
// declaration order. The first-declared member 'a' streams first, ending at the
// most significant end; were the order reversed the result would be 0xCDAB.
TEST(StreamExpressionConcat, StructMembersStreamedInDeclarationOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } st;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    st.a = 8'hAB;\n"
      "    st.b = 8'hCD;\n"
      "    dst = {>> {st}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

// §11.4.14.1: an untagged union is streamed by applying the procedure to its
// first-declared member only. Both members are 8 bits and overlap the same
// storage; streaming only the first yields an 8-bit stream, which lands
// left-aligned in the 16-bit target as 0xAB00. Streaming both members would
// instead pack 16 bits (0xABAB).
TEST(StreamExpressionConcat, UntaggedUnionStreamsFirstMemberOnly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    u.a = 8'hAB;\n"
      "    dst = {>> {u}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAB00u);
}

// §11.4.14.1: a null class handle is skipped (not streamed). The handle h is
// left null and contributes nothing, so the generic stream carries only the
// trailing scalar's 8 bits, landing left-aligned in the 16-bit target.
TEST(StreamExpressionConcat, NullClassHandleSkipped) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCD00u);
}

// §11.4.14.1: a non-null class handle is streamed by applying the procedure to
// each data member of the referenced object in declaration order, with an
// extended class streaming its base-class members before its own. Base members
// b0, b1 precede derived member d, so b0 lands at the most significant end and
// d at the least; any other ordering would change the packed value.
TEST(StreamExpressionConcat, NonNullClassHandleStreamsBaseFirstInDeclOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

}  // namespace
