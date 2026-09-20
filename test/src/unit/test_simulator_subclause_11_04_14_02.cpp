#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StreamReordering, StreamingRightShiftIntegration) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {>> {8'hAB}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(StreamReordering, StreamingLeftShiftIntegration) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {<< {8'hAB}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xD5u);
}

// §11.4.14.2: a slice_size given as a simple type names a block width equal to
// that type's number of bits. Driven from real source (not a hand-built Expr)
// so the parser records the `byte` type as the slice_size and the simulator
// resolves it to an 8-bit block width: streaming 16'hABCD with `<<` in byte
// blocks reverses the two bytes to 0xCDAB.
TEST(StreamReordering, TypeSliceSizeByteReversesBytesRealSource) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  initial result = {<< byte {16'hABCD}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDABu);
}

// §11.4.14.2: "if a type is used, the block size shall be the number of bits in
// that type." A `shortint` slice is 16 bits, so streaming a 32-bit value with
// `<<` swaps the two 16-bit halves (0xABCD1234 -> 0x1234ABCD) -- the same
// re-ordering an explicit `<< 16` produces. Distinguishing this from a whole-
// value single block confirms the type is resolved to its bit width rather than
// treated as one indivisible block.
TEST(StreamReordering, TypeSliceSizeShortintUsesTypeBitWidthRealSource) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = {<< shortint {32'hABCD1234}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234ABCDu);
}

// §11.4.14.2: the slice_size may be a constant integral expression, and
// §11.2.1 admits a parameter as such a constant. This is a distinct code path
// from a bare literal: the parameter is elaborated and lowered to a runtime
// constant, then the streaming evaluator folds `(WIDTH+0)` to 8 at run time.
// Built from real source and run end-to-end: an 8-bit block size slices
// 16'hABCD into two bytes and reverses them to 0xCDAB. A wrong resolution
// (e.g. defaulting the name to a 32-bit width) would leave 0xABCD unreordered.
TEST(StreamReordering, ParameterSliceSizeResolvesToBlockWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter WIDTH = 8;\n"
      "  logic [15:0] result;\n"
      "  initial result = {<< (WIDTH+0) {16'hABCD}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDABu);
}

TEST(StreamReordering, RightShiftIgnoresSliceSizeNonDivisible) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [5:0] result;\n"
      "  initial result = {>> 4 {6'b110101}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b110101u);
}

TEST(StreamReordering, LeftShiftShortLastBlock) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [5:0] result;\n"
      "  initial result = {<< 4 {6'b110101}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b010111u);
}

TEST(StreamReordering, LeftShift16BitSliceSwap) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = {<< 16 {32'hABCD1234}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234ABCDu);
}

TEST(StreamReordering, LeftShiftSliceSizeEqualsWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {<< 8 {8'hAB}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(StreamReordering, NestedStreamingReordering) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] result;\n"
      "  initial result = {<< 2 { {<< {4'b1101}} }};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b1110u);
}

// §11.4.14.2: it shall be an error for a slice_size constant expression to be
// zero or negative. The pack side reports it, and the report names §11.4.14.2.
TEST(StreamReordering, PackZeroSliceSizeNames11_4_14_2) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter SZ = 8;\n"
      "  logic [15:0] result;\n"
      "  initial result = {<< (SZ-8) {16'hABCD}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice_size for streaming operator", 4,
                            "11.4.14.2"));
}

// §11.4.14.2: the unpack side resolves the slice_size on its own path, and the
// report it raises names the same subclause.
TEST(StreamReordering, UnpackZeroSliceSizeNames11_4_14_2) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter SZ = 4;\n"
      "  logic [7:0] p, q;\n"
      "  initial {<< (SZ-4) {p, q}} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice_size for streaming operator", 4,
                            "11.4.14.2"));
}

// §11.4.14.2: `<<` reverses the order of the blocks and keeps the order of the
// bits within each, so two 96-bit blocks swap whole. The source is A:B with A
// 0x0123456789ABCDEF0F1E2D3C and B 0xFEDCBA98765432100F0FA5A5, and the stream
// is B:A: word 0 the low 64 bits of A, word 1 B's low 32 bits over A's high 32,
// word 2 B's high 64. Moved through a 64-bit carrier in two takes, the second
// shifted by 64 -- which the hardware wraps to 0 -- each block's high 32 bits
// landed over its low 32 (word 0 reading 0x89ABCDEF0F3F6D7F) and reappeared in
// the block's high word; every word tells the two apart.
TEST(StreamReordering, LeftShiftWideBlocksSwapWhole) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [191:0] result;\n"
      "  initial result = {<< 96 {192'h0123_4567_89AB_CDEF_0F1E_2D3C_"
      "FEDC_BA98_7654_3210_0F0F_A5A5}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 3u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0x89ABCDEF0F1E2D3Cu);
  EXPECT_EQ(var->value.words[1].aval, 0x0F0FA5A501234567u);
  EXPECT_EQ(var->value.words[2].aval, 0xFEDCBA9876543210u);
}

// §11.4.14.2: the last (left-most) block has the size of the remaining bits,
// neither padded nor truncated. 160 bits sliced by 96 leave a 64-bit block H
// (0xABCDEF0123456789) above the 96-bit block L (0xFEDCBA98765432100F0FA5A5);
// the stream is L:H, H filling word 0 exactly and L words 1 and 2. A block
// deposited at its full slice_size would carry 32 zero bits over the bottom of
// L; a block moved through the 64-bit carrier would mangle L as above.
TEST(StreamReordering, LeftShiftWideShortLastBlockKeepsItsSize) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [159:0] result;\n"
      "  initial result = {<< 96 {160'hABCD_EF01_2345_6789_"
      "FEDC_BA98_7654_3210_0F0F_A5A5}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 3u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0xABCDEF0123456789u);
  EXPECT_EQ(var->value.words[1].aval, 0x765432100F0FA5A5u);
  EXPECT_EQ(var->value.words[2].aval, 0xFEDCBA98u);
}

}  // namespace
