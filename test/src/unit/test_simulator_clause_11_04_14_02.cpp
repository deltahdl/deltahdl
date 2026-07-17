#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StreamReordering, StreamingRightShiftIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {>> {8'hAB}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(StreamReordering, StreamingLeftShiftIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {<< {8'hAB}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  initial result = {<< byte {16'hABCD}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = {<< shortint {32'hABCD1234}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter WIDTH = 8;\n"
      "  logic [15:0] result;\n"
      "  initial result = {<< (WIDTH+0) {16'hABCD}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDABu);
}

TEST(StreamReordering, RightShiftIgnoresSliceSizeNonDivisible) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] result;\n"
      "  initial result = {>> 4 {6'b110101}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b110101u);
}

TEST(StreamReordering, LeftShiftShortLastBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] result;\n"
      "  initial result = {<< 4 {6'b110101}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b010111u);
}

TEST(StreamReordering, LeftShift16BitSliceSwap) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = {<< 16 {32'hABCD1234}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234ABCDu);
}

TEST(StreamReordering, LeftShiftSliceSizeEqualsWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {<< 8 {8'hAB}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(StreamReordering, NestedStreamingReordering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] result;\n"
      "  initial result = {<< 2 { {<< {4'b1101}} }};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b1110u);
}

}  // namespace
