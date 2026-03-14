#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, UnsizedDecimal) {
  auto r = LexOne("659 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "659");
}

TEST(LexicalConventionLexing, UnsizedDecimalZero) {
  auto r = LexOne("0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "0");
}

TEST(LexicalConventionLexing, UnsizedHex) {
  auto r = LexOne("'h837FF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'h837FF");
}

TEST(LexicalConventionLexing, UnsizedOctal) {
  auto r = LexOne("'o7460 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'o7460");
}

TEST(LexicalConventionLexing, SizedBinary) {
  auto r = LexOne("4'b1001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'b1001");
}

TEST(LexicalConventionLexing, SizedDecimal) {
  auto r = LexOne("5'D3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "5'D3");
}

TEST(LexicalConventionLexing, SizedHex) {
  auto r = LexOne("8'hFF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'hFF");
}

TEST(LexicalConventionLexing, SizedOctal) {
  auto r = LexOne("8'o77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'o77");
}

TEST(LexicalConventionLexing, SignedHex) {
  auto r = LexOne("4'shf ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'shf");
}

TEST(LexicalConventionLexing, SignedDecimal) {
  auto r = LexOne("8'sd99 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'sd99");
}

TEST(LexicalConventionLexing, SignedUpperS) {
  auto r = LexOne("4'Shf ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'Shf");
}

TEST(LexicalConventionLexing, BaseUpperH) {
  auto r = LexOne("8'HAB ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, BaseUpperB) {
  auto r = LexOne("4'B1010 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, BaseUpperO) {
  auto r = LexOne("8'O77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, WhitespaceSizeAndBase) {
  auto r = LexOne("5 'D 3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, WhitespaceBaseAndDigits) {
  auto r = LexOne("32 'h 12ab_f001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, XValueInHex) {
  auto r = LexOne("12'hx ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, ZValueInHex) {
  auto r = LexOne("16'hz ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, QuestionMarkInBinary) {
  auto r = LexOne("4'b? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, QuestionMarkSigned) {
  auto r = LexOne("16'sd? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, UnderscoreInDecimal) {
  auto r = LexOne("27_195_000 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "27_195_000");
}

TEST(LexicalConventionLexing, UnderscoreInBinary) {
  auto r = LexOne("16'b0011_0101_0001_1111 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, UnderscoreInHex) {
  auto r = LexOne("32'h12ab_f001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, UnbasedUnsizedZero) {
  auto r = LexOne("'0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
  EXPECT_EQ(r.token.text, "'0");
}

TEST(LexicalConventionLexing, UnbasedUnsizedOne) {
  auto r = LexOne("'1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
  EXPECT_EQ(r.token.text, "'1");
}

TEST(LexicalConventionLexing, UnbasedUnsizedX) {
  auto r = LexOne("'x ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexicalConventionLexing, UnbasedUnsizedZ) {
  auto r = LexOne("'z ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexicalConventionLexing, UnbasedUnsizedUpperX) {
  auto r = LexOne("'X ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexicalConventionLexing, UnbasedUnsizedUpperZ) {
  auto r = LexOne("'Z ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexicalConventionLexing, NoDigitsAfterBaseError) {
  auto [tokens, errors] = LexWithDiag("8'd-6");
  EXPECT_TRUE(errors);
}

TEST(LexicalConventionLexing, DecimalXZMixedError) {
  auto [tokens, errors] = LexWithDiag("8'd1x");
  EXPECT_TRUE(errors);
}

TEST(LexicalConventionLexing, DecimalXZMultiError) {
  auto [tokens, errors] = LexWithDiag("8'dxz");
  EXPECT_TRUE(errors);
}

TEST(LexicalConventionLexing, HexDigitsCaseInsensitive) {
  auto r1 = LexOne("8'habcd ");
  auto r2 = LexOne("8'hABCD ");
  EXPECT_EQ(r1.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r2.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, LargeUnsizedHex) {
  auto r = LexOne("'h7_0000_0000 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralConstants, SizedHexLiteralValue) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 20'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

}  // namespace
TEST(IntegerLiteralConstants, WhitespaceBetweenSizeAndBase) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 5 'd 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}
