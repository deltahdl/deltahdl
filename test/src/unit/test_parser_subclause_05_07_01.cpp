#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/parser.h"

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

TEST(IntegerLiteralParsing, ZeroSizeError) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 0'hFF;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diag->Diagnostics(),
                            "size of integer literal shall be nonzero", 2,
                            "5.7.1"));
  delete r.diag;
}

TEST(IntegerLiteralParsing, UnaryMinusOnSimpleDecimal) {
  auto r = Parse("module m; int x; initial x = -42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->lhs->int_val, 42u);
}

TEST(IntegerLiteralParsing, UnaryPlusOnSimpleDecimal) {
  auto r = Parse("module m; int x; initial x = +42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->lhs->int_val, 42u);
}

TEST(IntegerLiteralParsing, UnaryMinusOnBasedLiteral) {
  auto r = Parse("module m; logic [7:0] x; initial x = -8'd6; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->lhs->int_val, 6u);
}

// §5.7.1: a plus operator preceding the size of a based literal is a unary plus
// operator applied to the literal (the based-literal counterpart of the unary
// plus on a simple decimal).
TEST(IntegerLiteralParsing, UnaryPlusOnBasedLiteral) {
  auto r = Parse("module m; logic [7:0] x; initial x = +8'd6; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->lhs->int_val, 6u);
}

// §5.7.1 sizes a based literal by its size constant, so the digits of a 96-bit
// hexadecimal literal reach beyond the 64 bits Expr::int_val holds; int_val
// holds the low 64 bits, which the elaborator folds. Each digit position
// differs from the one 64 places above it, so a fold keeping the high bits or
// leaving zero reads a different number.
TEST(IntegerLiteralParsing, WideHexLiteralFoldsItsLowSixtyFourBits) {
  auto r = Parse(
      "module m;\n"
      "  logic [95:0] x;\n"
      "  initial x = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0x89ABCDEF00112233u);
}

// A decimal literal's digits are folded in base 10 with the same wrap: 2^80 + 1
// written out is 1208925819614629174706177, whose residue modulo 2^64 is 1. A
// fold that gave up on overflow read 0, and one that stopped before the digit
// taking the value past 64 bits would read the prefix 12089258196146291747.
TEST(IntegerLiteralParsing, WideDecimalLiteralFoldsModuloTwoToTheSixtyFour) {
  auto r = Parse(
      "module m;\n"
      "  logic [79:0] x;\n"
      "  initial x = 80'd1208925819614629174706177;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 1u);
}

// A 70-bit binary literal whose six digits above bit 63 are all ones and whose
// low 64 bits set bit 63 and bit 0 alone: int_val is those low 64 bits, so the
// six high digits fall away and bit 63 stays.
TEST(IntegerLiteralParsing, WideBinaryLiteralFoldsItsLowSixtyFourBits) {
  auto r = Parse(
      "module m;\n"
      "  logic [69:0] x;\n"
      "  initial x = 70'b111111_1000_0000_0000_0000_0000_0000_0000_0000"
      "_0000_0000_0000_0000_0000_0000_0000_0001;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0x8000000000000001u);
}

// §5.7.1 (printed page 77) composes a based literal of up to three tokens, its
// size, its base and its digits, and §5.4 makes a comment a token separator as
// §5.3's white space is, so `8 /* c */ 'h11` is the one sized literal 8'h11.
// The lexer reads the size and the base as one token across spaces and tabs
// alone; across the comment the size was a decimal literal of its own and
// `'h11` a second literal, which the parser reported as a stray token. The
// digit in the comment discriminates a join that read the source between the
// two tokens as part of the size.
TEST(IntegerLiteralParsing, BlockCommentBetweenSizeAndBaseJoinsOneLiteral) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 8 /* 2 */ 'h11;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->text, "8 'h11");
  EXPECT_EQ(rhs->int_val, 0x11u);
}

// §5.3 counts a newline as white space, so a size on one line and its base on
// the next are the same three-token literal, here with a one-line comment
// ending the first line.
TEST(IntegerLiteralParsing, LineCommentBetweenSizeAndBaseJoinsOneLiteral) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 4 // c\n"
      "    'sd3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->text, "4 'sd3");
  EXPECT_EQ(rhs->int_val, 3u);
}

}  // namespace
