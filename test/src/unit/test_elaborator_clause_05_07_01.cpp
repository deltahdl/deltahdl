// §5.7.1

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

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

static Expr* MakeSizedLiteral(Arena& arena, std::string_view text,
                              uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->text = text;
  e->int_val = val;
  return e;
}

namespace {

TEST(UnbasedUnsizedLiterals, AllOnesAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  assign x = '1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegerLiteralConstants, UnsizedDecimalAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegerLiteralConstants, UnsizedDecimalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 255;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegerLiteralConstants, BinaryNumberElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'b10101010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegerLiteralConstants, OctalNumberElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'o77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(HexNumberLiterals, HexNumberElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegerLiteralConstants, DecimalSizedBaseElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd200;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DecimalBasedLiterals, XDigitAllBitsUnknown) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DecimalLiteralConstants, DecimalZDigitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegerLiteralConstants, SignedDecimalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'sd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegerLiteralConstants, SignedBinaryElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'sb1010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegerLiteralConstants, SignedOctalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'so77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SignedIntegerLiterals, SignedHexElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'shAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnbasedUnsizedLiterals, ZeroLiteralElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = '0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnbasedUnsizedLiterals, UnbasedUnsizedOneElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = '1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnbasedUnsizedLiterals, XLiteralElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 'x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnbasedUnsizedLiterals, ZLiteralElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 'z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntegerLiteralConstants, UnderscoredDecimalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial x = 1_000;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DecimalLiterals, XDigitSetsAllBitsUnknown) {
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
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(OctalLiterals, UnderscoreSeparatorInValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 12'o77_77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 07777u);
}

TEST(IntegerLiteralConstants, HexValueUnderscoreSeparator) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 16'hAB_CD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(IntegerLiteralConstants, HexDigitsCaseInsensitive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  initial begin\n"
      "    a = 16'hABcd;\n"
      "    b = 16'habCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), vb->value.ToUint64());
  EXPECT_EQ(va->value.ToUint64(), 0xABCDu);
}

TEST(IntegerLiteralConstants, UnderscoreSeparator) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 27_195_000;\n"
      "    b = 16'b0011_0101_0001_1111;\n"
      "    c = 32'h12ab_f001;\n"
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
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 27195000u);
  EXPECT_EQ(vb->value.ToUint64(), 0x351Fu);
  EXPECT_EQ(vc->value.ToUint64(), 0x12ABF001u);
}

TEST(HexLiteralXValue, AllBitsUnknownWhenXDigit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 12'hx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(SimClause05, Cl5_7_1_ZValueInHexLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 16'hz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint16_t mask = 0xFFFF;
  EXPECT_EQ(var->value.words[0].aval & mask, 0u);
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

TEST(SimClause05, Cl5_7_1_XInBinaryLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] x;\n"
      "  initial x = 3'b01x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x7, 0b011u);
  EXPECT_EQ(var->value.words[0].bval & 0x7, 0b001u);
}

TEST(SimClause05, Cl5_7_1_QuestionMarkAsZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'b1?0?;\n"
      "    b = 4'b1z0z;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerRunAndCompareBitPatterns(f, design, 0xF);
}

TEST(SimClause05, Cl5_7_1_UnbasedUnsizedLiteral01) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  initial begin\n"
      "    a = '0;\n"
      "    b = '1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0u);
  EXPECT_EQ(vb->value.ToUint64(), 0xFFFFu);
}

TEST(SimClause05, Cl5_7_1_UnbasedUnsizedLiteralXZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  initial begin\n"
      "    a = 'x;\n"
      "    b = 'z;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  uint16_t mask = 0xFFFF;
  EXPECT_EQ(va->value.words[0].aval & mask, mask);
  EXPECT_EQ(va->value.words[0].bval & mask, mask);
  EXPECT_EQ(vb->value.words[0].aval & mask, 0u);
  EXPECT_EQ(vb->value.words[0].bval & mask, mask);
}

TEST(SimClause05, Cl5_7_1_LeftPadWithX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 'hx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint16_t mask = 0xFFF;
  EXPECT_EQ(var->value.words[0].aval & mask, mask);
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

TEST(SimClause05, Cl5_7_1_LeftPadWithZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 'hz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint16_t mask = 0xFFF;
  EXPECT_EQ(var->value.words[0].aval & mask, 0u);
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

TEST(SimClause05, Cl5_7_1_SignedDesignatorBitPattern) {
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

TEST(SimClause05, Cl5_7_1_XZCaseInsensitive) {
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

TEST(SimClause05, Cl5_7_1_XInOctalLiteral) {
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

TEST(SimClause05, Cl5_7_1_BaseFormatCaseInsensitive) {
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

TEST(SimClause05, Cl5_7_1_LeftPadKnownHex) {
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
  EXPECT_EQ(var->value.words[0].aval & 0xFFF, 0x03Fu);
  EXPECT_EQ(var->value.words[0].bval & 0x00F, 0x00Fu);
  EXPECT_EQ(var->value.words[0].bval & 0xF00, 0x000u);
}

TEST(SimClause05, Cl5_7_1_DecimalSingleDigitX) {
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

TEST(SimClause05, Cl5_7_1_SignedBaseLiteralIsSigned) {
  SimFixture f;
  auto* lit = MakeSizedLiteral(f.arena, "4'sd3", 3);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(SimClause05, Cl5_7_1_UnsignedBaseLiteralNotSigned) {
  SimFixture f;
  auto* lit = MakeSizedLiteral(f.arena, "4'd3", 3);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(SimClause05, Cl5_7_1_SignedHexLiteralIsSigned) {
  SimFixture f;
  auto* lit = MakeSizedLiteral(f.arena, "8'shFF", 0xFF);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(SimClause05, Cl5_7_1_SizedHexLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 20'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

TEST(SimClause05, Cl5_7_1_LeftPadWithZeros) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x0Fu);
}

TEST(SimClause05, Cl5_7_1_WhiteSpaceSizeAndBase) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 5 'd 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

TEST(SimClause05, Cl5_7_1_SizeConstantNonzero) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 1u);
}

}  // namespace
