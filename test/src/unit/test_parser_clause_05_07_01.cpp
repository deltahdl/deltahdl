#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(IntegerLiteralParsing, UnsizedDecimal) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 659;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 659u);
}

TEST(IntegerLiteralParsing, DecimalZero) {
  auto r = Parse("module m; int x; initial x = 0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0u);
}

TEST(IntegerLiteralParsing, SizedBinary) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 4'b1001;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0b1001u);
}

TEST(IntegerLiteralParsing, SizedHex) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 8'hFF;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xFFu);
}

TEST(IntegerLiteralParsing, SizedOctal) {
  EXPECT_TRUE(ParseOk("module m; initial x = 8'o77; endmodule"));
}

TEST(IntegerLiteralParsing, SizedDecimal) {
  EXPECT_TRUE(ParseOk("module m; initial x = 5'D3; endmodule"));
}

TEST(IntegerLiteralParsing, UnsizedHex) {
  EXPECT_TRUE(ParseOk("module m; initial x = 'h837FF; endmodule"));
}

TEST(IntegerLiteralParsing, LargeUnsizedHex) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [63:0] big;\n"
              "  initial big = 'h7_0000_0000;\n"
              "endmodule"));
}

TEST(IntegerLiteralParsing, SignedLiteral) {
  EXPECT_TRUE(ParseOk("module m; initial x = 4'shf; endmodule"));
}

TEST(IntegerLiteralParsing, SignedDecimalQuestion) {
  EXPECT_TRUE(ParseOk("module m; initial x = 16'sd?; endmodule"));
}

TEST(IntegerLiteralParsing, NegativeUnsized) {
  EXPECT_TRUE(ParseOk("module m; initial x = -8'd6; endmodule"));
}

TEST(IntegerLiteralParsing, XValue) {
  EXPECT_TRUE(ParseOk("module m; initial x = 12'hx; endmodule"));
}

TEST(IntegerLiteralParsing, ZValue) {
  EXPECT_TRUE(ParseOk("module m; initial x = 16'hz; endmodule"));
}

TEST(IntegerLiteralParsing, QuestionMark) {
  EXPECT_TRUE(ParseOk("module m; initial x = 4'b?; endmodule"));
}

TEST(IntegerLiteralParsing, DecimalXDigit) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'dx; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, DecimalZDigit) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'dz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, UnderscoreInBinary) {
  EXPECT_TRUE(
      ParseOk("module m; initial x = 16'b0011_0101_0001_1111; endmodule"));
}

TEST(IntegerLiteralParsing, UnderscoreInDecimal) {
  auto r = Parse("module m; int x; initial x = 1_000_000; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 1000000u);
}

TEST(IntegerLiteralParsing, SpaceBetweenBaseAndDigits) {
  EXPECT_TRUE(ParseOk("module m; initial x = 32 'h 12ab_f001; endmodule"));
}

TEST(IntegerLiteralParsing, DecimalBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'd99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

TEST(IntegerLiteralParsing, DecimalBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'D99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

TEST(IntegerLiteralParsing, BinaryBaseLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'b1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

TEST(IntegerLiteralParsing, BinaryBaseUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'B1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

TEST(IntegerLiteralParsing, OctalBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'o77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

TEST(IntegerLiteralParsing, OctalBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'O77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

TEST(IntegerLiteralParsing, HexBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'hAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

TEST(IntegerLiteralParsing, HexBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'HAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

TEST(IntegerLiteralParsing, SignedDecimalLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'sd99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

TEST(IntegerLiteralParsing, SignedDecimalUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SD99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

TEST(IntegerLiteralParsing, SignedBinaryLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'sb1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

TEST(IntegerLiteralParsing, SignedBinaryUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'SB1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

TEST(IntegerLiteralParsing, SignedOctalLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'so77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

TEST(IntegerLiteralParsing, SignedOctalUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SO77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

TEST(IntegerLiteralParsing, SignedHexLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'shAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

TEST(IntegerLiteralParsing, SignedHexUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SHAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

TEST(IntegerLiteralParsing, HexDigitLowercase) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'habcdef; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDEFu);
}

TEST(IntegerLiteralParsing, HexDigitUppercase) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'hABCDEF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDEFu);
}

TEST(IntegerLiteralParsing, OctalDigitAll) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'o01234567; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 01234567u);
}

TEST(IntegerLiteralParsing, BinaryDigitZeroOne) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'b0101; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 5u);
}

TEST(IntegerLiteralParsing, DecimalDigitAll) {
  auto r = Parse("module m; int x; initial x = 1234567890; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 1234567890u);
}

TEST(IntegerLiteralParsing, UnbasedUnsizedZero) {
  auto r = Parse("module m; logic x; initial x = '0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralParsing, UnbasedUnsizedOne) {
  auto r = Parse("module m; logic x; initial x = '1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralParsing, UnbasedUnsizedX) {
  auto r = Parse("module m; logic x; initial x = 'x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralParsing, UnbasedUnsizedZ) {
  auto r = Parse("module m; logic x; initial x = 'z; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralParsing, UnbasedUnsizedInAssign) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  assign x = '1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstContAssignRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralParsing, BinaryValueWithUnderscores) {
  auto r =
      Parse("module m; logic [7:0] x; initial x = 8'b1010_1010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xAAu);
}

TEST(IntegerLiteralParsing, OctalValueWithUnderscores) {
  auto r =
      Parse("module m; logic [11:0] x; initial x = 12'o77_77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 07777u);
}

TEST(IntegerLiteralParsing, HexValueWithUnderscores) {
  auto r =
      Parse("module m; logic [15:0] x; initial x = 16'hAB_CD; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDu);
}

TEST(IntegerLiteralParsing, Size1Bit) {
  auto r = Parse("module m; logic x; initial x = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 1u);
}

TEST(IntegerLiteralParsing, Size32Bit) {
  auto r = Parse("module m; int x; initial x = 32'd100; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 100u);
}

TEST(IntegerLiteralParsing, ConstantPrimaryInteger) {
  auto r = Parse("module m; parameter int P = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, MultipleLiterals) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = 42; b = 8'hFF; c = 4'b1010; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

struct ParseDiagResult {
  SourceManager mgr;
  Arena arena;
  DiagEngine* diag = nullptr;
  CompilationUnit* cu = nullptr;
};

static ParseDiagResult ParseWithDiag(const std::string& src) {
  ParseDiagResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  result.diag = new DiagEngine(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, *result.diag);
  Parser parser(lexer, result.arena, *result.diag);
  result.cu = parser.Parse();
  return result;
}

TEST(IntegerLiteralParsing, SizedNoOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(IntegerLiteralParsing, SizedOverflowWarning) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hFF;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
}

TEST(IntegerLiteralParsing, SizedExactFit) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(IntegerLiteralParsing, SizedOneBitOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 3'b1111;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
}

TEST(IntegerLiteralParsing, UnsignedDecimal) {
  auto r = Parse("module m; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, UnsignedDecimalWithUnderscore) {
  auto r = Parse("module m; initial x = 1_000_000; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, SizedDecimalBaseD) {
  auto r = Parse("module m; initial x = 8'd255; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, SignedDecimal) {
  auto r = Parse("module m; initial x = 8'sd127; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, XDigitUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'hX; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, ZDigitLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'hz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, DecimalBaseXDigit) {
  auto r = Parse("module m; initial x = 4'dx; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, DecimalBaseZDigit) {
  auto r = Parse("module m; initial x = 4'dz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, DecimalBaseQuestionMark) {
  auto r = Parse("module m; initial x = 4'h?; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, BinaryNumber) {
  auto r = Parse("module m; initial x = 4'b1010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, SignedBinaryNumber) {
  auto r = Parse("module m; initial x = 4'sb1010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, BinaryWithUnderscore) {
  auto r = Parse("module m; initial x = 8'b1010_0101; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, BinaryWithXZ) {
  auto r = Parse("module m; initial x = 4'b10xz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, OctalNumber) {
  auto r = Parse("module m; initial x = 8'o77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, SignedOctalNumber) {
  auto r = Parse("module m; initial x = 8'so77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, HexNumber) {
  auto r = Parse("module m; initial x = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, SignedHexNumber) {
  auto r = Parse("module m; initial x = 8'shFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, HexWithUnderscore) {
  auto r = Parse("module m; initial x = 32'hDEAD_BEEF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, UnsizedHexShort) {
  auto r = Parse("module m; initial x = 'hAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, UnsizedBinary) {
  auto r = Parse("module m; initial x = 'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, UnsizedOctal) {
  auto r = Parse("module m; initial x = 'o7; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, UnbasedUnsizedZeroBare) {
  auto r = Parse("module m; initial x = '0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralParsing, UnbasedUnsizedOneBare) {
  auto r = Parse("module m; initial x = '1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralParsing, UnbasedUnsizedXBare) {
  auto r = Parse("module m; initial x = 'x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralParsing, UnbasedUnsizedZBare) {
  auto r = Parse("module m; initial x = 'z; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralParsing, ZeroSizeError) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 0'hFF;\n"
      "endmodule\n");
  EXPECT_TRUE(r.diag->HasErrors() || r.diag->WarningCount() > 0u);
  delete r.diag;
}

TEST(IntegerLiteralParsing, NegativeBeforeSizedLiteral) {
  auto r = Parse("module m; logic [7:0] x; initial x = -8'd6; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralParsing, QuestionMarkInOctal) {
  auto r = Parse("module m; logic [5:0] x; initial x = 6'o?; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, QuestionMarkInHex) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'h?; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, UnsizedDecimalBase) {
  auto r = Parse("module m; int x; initial x = 'd42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, DecimalValueWithUnderscores) {
  auto r = Parse("module m; int x; initial x = 27_195_000; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 27195000u);
}

TEST(IntegerLiteralParsing, UnsizedUnbasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 12u);
}

TEST(IntegerLiteralParsing, UnsizedBasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 'd12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, SizedBasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 16'd12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, NegativeUnsizedIsTwosComplement) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), -4);
}

TEST(IntegerLiteralParsing, BinaryLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 4'b1010;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xAu);
}

TEST(IntegerLiteralParsing, IntegerLiteralInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [31:0] x;\n"
              "  initial x = 32'd42;\n"
              "endmodule\n"));
}

TEST(IntegerLiteralParsing, UnbasedUnsizedLiteralInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [15:0] x;\n"
              "  assign x = '1;\n"
              "endmodule\n"));
}

}  // namespace
