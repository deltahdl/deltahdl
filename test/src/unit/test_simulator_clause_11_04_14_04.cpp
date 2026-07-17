#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StreamingDynamicDataSim, PackWithSlicesSelectedElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    arr[2] = 8'hCC;\n"
      "    arr[3] = 8'hDD;\n"
      "    result = {>> byte {arr with [0 +: 2]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBu);
}

TEST(StreamingDynamicDataSim, PackWithFixedRangeSelectsSubset) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    arr[2] = 8'hCC;\n"
      "    arr[3] = 8'hDD;\n"
      "    result = {>> byte {arr with [1:2]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBBCCu);
}

TEST(StreamingDynamicDataSim, PackWithSimpleIndexSelectsSingleElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    arr[2] = 8'hCC;\n"
      "    arr[3] = 8'hDD;\n"
      "    result = {>> byte {arr with [2]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCCu);
}

TEST(StreamingDynamicDataSim, UnpackPartialRangeKeepsRemainder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  initial begin\n"
      "    arr[0] = 8'h11;\n"
      "    arr[1] = 8'h22;\n"
      "    arr[2] = 8'h33;\n"
      "    arr[3] = 8'h44;\n"
      "    {>> byte {arr with [0 +: 2]}} = 16'hAABB;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBBu);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x33u);
  EXPECT_EQ(f.ctx.FindVariable("arr[3]")->value.ToUint64(), 0x44u);
}

TEST(StreamingDynamicDataSim, UnpackFixedRangeModifiesOnlySpecified) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  initial begin\n"
      "    arr[0] = 8'h11;\n"
      "    arr[1] = 8'h22;\n"
      "    arr[2] = 8'h33;\n"
      "    arr[3] = 8'h44;\n"
      "    {>> byte {arr with [1:2]}} = 16'hEEFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11u);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xEEu);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xFFu);
  EXPECT_EQ(f.ctx.FindVariable("arr[3]")->value.ToUint64(), 0x44u);
}

TEST(StreamingDynamicDataSim, UnpackOutOfRangeOnFixedArrayErrors) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  initial begin\n"
      "    {>> byte {arr with [0 +: 8]}} = 64'hDEADBEEFCAFEBABE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StreamingDynamicDataSim, UnpackResizesDynamicArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  initial begin\n"
      "    {<< byte {q with [0 +: 3]}} = 24'hAABBCC;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  if (q) {
    EXPECT_EQ(q->elements.size(), 3u);
  }
}

TEST(StreamingDynamicDataSim, GreedyUnpackFirstDynamicGetsAllData) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  logic [7:0] trailer;\n"
      "  initial begin\n"
      "    {>> byte {q, trailer}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  auto* t = f.ctx.FindVariable("trailer");
  if (q && t) {
    EXPECT_EQ(q->elements.size(), 3u);
    EXPECT_EQ(t->value.ToUint64(), 0xDDu);
  }
}

TEST(StreamingDynamicDataSim, GreedyUnpackRemainingDynamicLeftEmpty) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q1[$];\n"
      "  byte q2[$];\n"
      "  initial begin\n"
      "    {>> byte {q1, q2}} = 24'hAABBCC;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q1 = f.ctx.FindQueue("q1");
  auto* q2 = f.ctx.FindQueue("q2");
  if (q1 && q2) {
    EXPECT_EQ(q1->elements.size(), 3u);
    EXPECT_EQ(q2->elements.size(), 0u);
  }
}

// §11.4.14.4: a with-range that refers to a field unpacked to the left of its
// array (earlier in stream order) is evaluated with the value that this same
// operator just unpacked into that field. Here `len` is unpacked as 3, so the
// range [0 +: len] sizes the payload slice to exactly three bytes that receive
// the next three stream bytes; the trailing payload positions stay untouched.
TEST(StreamingDynamicDataSim, WithExprReferencesEarlierUnpackedData) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int len;\n"
      "  logic [7:0] payload[8];\n"
      "  initial begin\n"
      "    {>> {len, payload with [0 +: len]}} = {32'd3, 24'hAABBCC};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vlen = f.ctx.FindVariable("len");
  ASSERT_NE(vlen, nullptr);
  EXPECT_EQ(vlen->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("payload[0]")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("payload[1]")->value.ToUint64(), 0xBBu);
  EXPECT_EQ(f.ctx.FindVariable("payload[2]")->value.ToUint64(), 0xCCu);
}

// §11.4.14.4: the fourth array_range_expression form of Syntax 11-5 is the
// minus indexed part-select `[idx -: width]`, which selects `width` elements
// ending at `idx` (descending). Here [3 -: 2] picks the two elements at indices
// 2 and 3, so a right-shift pack (no re-ordering) places CC then DD into the
// stream. The other three range forms are exercised by sibling sim tests; this
// pins the minus-form resolver at the stage where it actually runs.
TEST(StreamingDynamicDataSim, PackWithMinusPartSelectSelectsTrailingElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    arr[2] = 8'hCC;\n"
      "    arr[3] = 8'hDD;\n"
      "    result = {>> byte {arr with [3 -: 2]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCCDDu);
}

TEST(StreamingDynamicDataSim, PackWithRangeLargerThanArrayUsesDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[2];\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    result = {>> byte {arr with [0 +: 4]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // §11.4.14.4: in a pack, a with-range wider than the array streams the whole
  // array and pads the surplus positions with the nonexistent-entry value
  // (§7.4.5). Both real bytes appear in the high half of the 32-bit result;
  // the two absent positions contribute the padding value in the low half.
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABB0000u);
}

// §11.4.14.4: a with-range expression that refers to a field unpacked to the
// right of its array (i.e. after the array in stream order) is evaluated with
// that field's previous value, not the value it receives during this unpack.
// Here `n` is 2 before the unpack, so the range [0 +: n] selects exactly two
// payload elements even though `n` itself is overwritten with 5 by the same
// operator. Using the post-unpack value (5) would change the element count and
// the bit alignment, so the asserted result pins the previous-value rule.
TEST(StreamingDynamicDataSim, WithRangeUsesPreviousValueOfLaterUnpackedField) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] payload[8];\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = 2;\n"
      "    {>> {payload with [0 +: n], n}} = 48'hAABB00000005;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("payload[0]")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("payload[1]")->value.ToUint64(), 0xBBu);
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 5u);
}

// §11.4.14.4: the expression before `with` may be a queue (a one-dimensional
// unpacked array). In a pack, a with-range selects the named slice of the
// queue exactly as it would for a fixed array, so only the two requested
// elements reach the stream.
TEST(StreamingDynamicDataSim, PackQueueWithRangeSelectsSubset) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    q.push_back(8'hAA);\n"
      "    q.push_back(8'hBB);\n"
      "    q.push_back(8'hCC);\n"
      "    result = {>> byte {q with [0 +: 2]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBu);
}

// §11.4.14.4: packing a queue with a with-range wider than its current size
// streams the whole queue and fills the surplus positions with the
// nonexistent-entry value (§7.4.5) — zero for a 2-state byte element. The two
// live bytes occupy the high half of the result; the two absent positions
// contribute the padding in the low half.
TEST(StreamingDynamicDataSim, PackQueueWithRangeBeyondSizeUsesDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    q.push_back(8'hAA);\n"
      "    q.push_back(8'hBB);\n"
      "    result = {>> byte {q with [0 +: 4]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABB0000u);
}

// §11.4.14.4: when an unpack with-range is smaller than the extent of a
// variable-size array, only the designated locations are written and the rest
// of the array is left unmodified. Here [1 +: 2] rewrites q[1] and q[2] while
// q[0] and q[3] keep their prior contents and the queue does not grow.
TEST(StreamingDynamicDataSim, UnpackQueuePartialRangeKeepsRemainder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  initial begin\n"
      "    q.push_back(8'h11);\n"
      "    q.push_back(8'h22);\n"
      "    q.push_back(8'h33);\n"
      "    q.push_back(8'h44);\n"
      "    {>> byte {q with [1 +: 2]}} = 16'hEEFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x11u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0xEEu);
  EXPECT_EQ(q->elements[2].ToUint64(), 0xFFu);
  EXPECT_EQ(q->elements[3].ToUint64(), 0x44u);
}

// §11.4.14.4 + §7.4.5 dependency e2e: when a pack with-range is wider than the
// array, the surplus positions are filled with the nonexistent array entry
// value of §7.4.5 (Table 7-1). For a 4-state element type that value is x, not
// zero. The ToUint64-based sibling tests cannot tell x from 0, so this one
// inspects the raw 4-state word: the two live bytes are known (AA,BB in the
// high half, bval clear) while the two absent positions carry x (bval set) in
// the low half — proving §7.4.5's 4-state fill flows into the stream.
TEST(StreamingDynamicDataSim, PackFourStateOversizeRangePadsWithX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[2];\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    result = {>> byte {arr with [0 +: 4]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // High half holds the two real bytes with all bits known; low half is the
  // §7.4.5 nonexistent value x (aval 0, every bit flagged unknown in bval).
  EXPECT_EQ(var->value.words[0].aval, 0xAABB0000u);
  EXPECT_EQ(var->value.words[0].bval, 0x0000FFFFu);
}

// §11.4.14.4: the expression before `with` may be any one-dimensional unpacked
// array; besides a fixed array and a queue this includes a dynamic array. Its
// live elements live in the backing store (the is_dynamic path), so a
// with-range slice of a dynamic array built from a real '{...} initializer must
// select the named subset just as it does for the other array forms. Here [0 +:
// 2] streams d[0] and d[1] into the byte stream, leaving d[2] out.
TEST(StreamingDynamicDataSim, PackDynamicArrayWithRangeSelectsSubset) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] d [] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  logic [15:0] result;\n"
      "  initial result = {>> byte {d with [0 +: 2]}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBu);
}

}  // namespace
