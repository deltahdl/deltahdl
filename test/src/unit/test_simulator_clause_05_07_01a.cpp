// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

static void LowerRunAndCompareBitPatterns(SimFixture& f, RtlirDesign* design,
                                          uint32_t mask) {
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.words[0].aval & mask, vb->value.words[0].aval & mask);
  EXPECT_EQ(va->value.words[0].bval & mask, vb->value.words[0].bval & mask);
}

namespace {

// ---------------------------------------------------------------------------
// 30. Signed designator does not affect bit pattern
// ---------------------------------------------------------------------------
TEST(SimCh50701, SignedDesignatorBitPattern) {
  // §5.7.1: The s designator affects interpretation, not the bit pattern.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'hf;\n"
      "    b = 4'shf;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerRunAndCompareBitPatterns(f, design, 0xF);
  auto* va = f.ctx.FindVariable("a");
  EXPECT_EQ(va->value.words[0].aval & 0xF, 0xFu);
}

// ---------------------------------------------------------------------------
// 31. X and z case insensitive in values
// ---------------------------------------------------------------------------
TEST(SimCh50701, XZCaseInsensitive) {
  // §5.7.1: x and z are case insensitive in number values.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'bx01x;\n"
      "    b = 4'bX01X;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerRunAndCompareBitPatterns(f, design, 0xF);
}

// ---------------------------------------------------------------------------
// 32. X in octal literal (sets 3 bits)
// ---------------------------------------------------------------------------
TEST(SimCh50701, XInOctalLiteral) {
  // §5.7.1: x sets 3 bits to unknown in octal base.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] x;\n"
      "  initial x = 6'o7x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x38, 0x38u);
  EXPECT_EQ(var->value.words[0].bval & 0x07, 0x07u);
}

// ---------------------------------------------------------------------------
// 33. Base format case insensitive
// ---------------------------------------------------------------------------
TEST(SimCh50701, BaseFormatCaseInsensitive) {
  // §5.7.1: Base format letter is case insensitive.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'HFF;\n"
      "    c = 8'b11111111;\n"
      "    d = 8'B11111111;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  auto* vc = f.ctx.FindVariable("c");
  auto* vd = f.ctx.FindVariable("d");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_NE(vc, nullptr);
  ASSERT_NE(vd, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xFFu);
  EXPECT_EQ(vb->value.ToUint64(), 0xFFu);
  EXPECT_EQ(vc->value.ToUint64(), 0xFFu);
  EXPECT_EQ(vd->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 34. White space between size and base format
// ---------------------------------------------------------------------------
TEST(SimCh50701, WhiteSpaceSizeAndBase) {
  // §5.7.1: White space allowed between size, base, and value tokens.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 5 'd 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

// ---------------------------------------------------------------------------
// 35. Left padding: known value (0x3x -> yields 03x)
// ---------------------------------------------------------------------------
TEST(SimCh50701, LeftPadKnownHex) {
  // §5.7.1: Known value with x in low nibble — yields 03x.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 'h3x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x: aval=1, bval=1. Lower nibble = x, middle = 3, upper = 0-pad.
  EXPECT_EQ(var->value.words[0].aval & 0xFFF, 0x03Fu);
  EXPECT_EQ(var->value.words[0].bval & 0x00F, 0x00Fu);
  EXPECT_EQ(var->value.words[0].bval & 0xF00, 0x000u);
}

// ---------------------------------------------------------------------------
// 36. Decimal single-digit x
// ---------------------------------------------------------------------------
TEST(SimCh50701, DecimalSingleDigitX) {
  // §5.7.1: Decimal literal allows single x/z/? digit only.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint8_t mask = 0xFF;
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

// ---------------------------------------------------------------------------
// 37. Size constant must be nonzero
// ---------------------------------------------------------------------------
TEST(SimCh50701, SizeConstantNonzero) {
  // §5.7.1: Size constant must be nonzero.
  // Using size=1 (the smallest legal size) verifies nonzero is accepted.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 1u);
}

}  // namespace
