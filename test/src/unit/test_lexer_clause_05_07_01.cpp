#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_7_1_UnsizedDecimal) {
  auto r = LexOne("659 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "659");
}

TEST(LexerClause05, Cl5_7_1_UnsizedDecimalZero) {
  auto r = LexOne("0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "0");
}

TEST(LexerClause05, Cl5_7_1_UnsizedHex) {
  auto r = LexOne("'h837FF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'h837FF");
}

TEST(LexerClause05, Cl5_7_1_UnsizedOctal) {
  auto r = LexOne("'o7460 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'o7460");
}

TEST(LexerClause05, Cl5_7_1_SizedBinary) {
  auto r = LexOne("4'b1001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'b1001");
}

TEST(LexerClause05, Cl5_7_1_SizedDecimal) {
  auto r = LexOne("5'D3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "5'D3");
}

TEST(LexerClause05, Cl5_7_1_SizedHex) {
  auto r = LexOne("8'hFF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'hFF");
}

TEST(LexerClause05, Cl5_7_1_SizedOctal) {
  auto r = LexOne("8'o77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'o77");
}

TEST(LexerClause05, Cl5_7_1_SignedHex) {
  auto r = LexOne("4'shf ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'shf");
}

TEST(LexerClause05, Cl5_7_1_SignedDecimal) {
  auto r = LexOne("8'sd99 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'sd99");
}

TEST(LexerClause05, Cl5_7_1_SignedUpperS) {
  auto r = LexOne("4'Shf ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'Shf");
}

TEST(LexerClause05, Cl5_7_1_BaseUpperH) {
  auto r = LexOne("8'HAB ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_BaseUpperB) {
  auto r = LexOne("4'B1010 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_BaseUpperO) {
  auto r = LexOne("8'O77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_WhitespaceSizeAndBase) {
  auto r = LexOne("5 'D 3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_WhitespaceBaseAndDigits) {
  auto r = LexOne("32 'h 12ab_f001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_XValueInHex) {
  auto r = LexOne("12'hx ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_ZValueInHex) {
  auto r = LexOne("16'hz ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_QuestionMarkInBinary) {
  auto r = LexOne("4'b? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_QuestionMarkSigned) {
  auto r = LexOne("16'sd? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_UnderscoreInDecimal) {
  auto r = LexOne("27_195_000 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "27_195_000");
}

TEST(LexerClause05, Cl5_7_1_UnderscoreInBinary) {
  auto r = LexOne("16'b0011_0101_0001_1111 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_UnderscoreInHex) {
  auto r = LexOne("32'h12ab_f001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_UnbasedUnsizedZero) {
  auto r = LexOne("'0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
  EXPECT_EQ(r.token.text, "'0");
}

TEST(LexerClause05, Cl5_7_1_UnbasedUnsizedOne) {
  auto r = LexOne("'1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
  EXPECT_EQ(r.token.text, "'1");
}

TEST(LexerClause05, Cl5_7_1_UnbasedUnsizedX) {
  auto r = LexOne("'x ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexerClause05, Cl5_7_1_UnbasedUnsizedZ) {
  auto r = LexOne("'z ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexerClause05, Cl5_7_1_UnbasedUnsizedUpperX) {
  auto r = LexOne("'X ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexerClause05, Cl5_7_1_UnbasedUnsizedUpperZ) {
  auto r = LexOne("'Z ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexerClause05, Cl5_7_1_NoDigitsAfterBaseError) {
  auto [tokens, errors] = LexWithDiag("8'd-6");
  EXPECT_TRUE(errors);
}

TEST(LexerClause05, Cl5_7_1_DecimalXZMixedError) {
  auto [tokens, errors] = LexWithDiag("8'd1x");
  EXPECT_TRUE(errors);
}

TEST(LexerClause05, Cl5_7_1_DecimalXZMultiError) {
  auto [tokens, errors] = LexWithDiag("8'dxz");
  EXPECT_TRUE(errors);
}

TEST(LexerClause05, Cl5_7_1_HexDigitsCaseInsensitive) {
  auto r1 = LexOne("8'habcd ");
  auto r2 = LexOne("8'hABCD ");
  EXPECT_EQ(r1.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r2.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_7_1_LargeUnsizedHex) {
  auto r = LexOne("'h7_0000_0000 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

}
