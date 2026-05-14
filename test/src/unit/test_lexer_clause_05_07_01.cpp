#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(IntegerLiteralLexing, UnsizedDecimal) {
  auto r = LexOne("659 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "659");
}

TEST(IntegerLiteralLexing, UnsizedDecimalZero) {
  auto r = LexOne("0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "0");
}

TEST(IntegerLiteralLexing, UnsizedHex) {
  auto r = LexOne("'h837FF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'h837FF");
}

TEST(IntegerLiteralLexing, UnsizedOctal) {
  auto r = LexOne("'o7460 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'o7460");
}

TEST(IntegerLiteralLexing, SizedBinary) {
  auto r = LexOne("4'b1001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'b1001");
}

TEST(IntegerLiteralLexing, SizedDecimal) {
  auto r = LexOne("5'D3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "5'D3");
}

TEST(IntegerLiteralLexing, SizedHex) {
  auto r = LexOne("8'hFF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'hFF");
}

TEST(IntegerLiteralLexing, SizedOctal) {
  auto r = LexOne("8'o77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'o77");
}

TEST(IntegerLiteralLexing, SignedHex) {
  auto r = LexOne("4'shf ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'shf");
}

TEST(IntegerLiteralLexing, SignedDecimal) {
  auto r = LexOne("8'sd99 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'sd99");
}

TEST(IntegerLiteralLexing, SignedUpperS) {
  auto r = LexOne("4'Shf ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'Shf");
}

TEST(IntegerLiteralLexing, BaseUpperH) {
  auto r = LexOne("8'HAB ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, BaseUpperB) {
  auto r = LexOne("4'B1010 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, BaseUpperO) {
  auto r = LexOne("8'O77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, WhitespaceSizeAndBase) {
  auto r = LexOne("5 'D 3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, WhitespaceBaseAndDigits) {
  auto r = LexOne("32 'h 12ab_f001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, XValueInHex) {
  auto r = LexOne("12'hx ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, ZValueInHex) {
  auto r = LexOne("16'hz ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, QuestionMarkInBinary) {
  auto r = LexOne("4'b? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, QuestionMarkSigned) {
  auto r = LexOne("16'sd? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, UnderscoreInDecimal) {
  auto r = LexOne("27_195_000 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "27_195_000");
}

TEST(IntegerLiteralLexing, UnderscoreInBinary) {
  auto r = LexOne("16'b0011_0101_0001_1111 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, UnderscoreInHex) {
  auto r = LexOne("32'h12ab_f001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, UnbasedUnsizedZero) {
  auto r = LexOne("'0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
  EXPECT_EQ(r.token.text, "'0");
}

TEST(IntegerLiteralLexing, UnbasedUnsizedOne) {
  auto r = LexOne("'1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
  EXPECT_EQ(r.token.text, "'1");
}

TEST(IntegerLiteralLexing, UnbasedUnsizedX) {
  auto r = LexOne("'x ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralLexing, UnbasedUnsizedZ) {
  auto r = LexOne("'z ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralLexing, UnbasedUnsizedUpperX) {
  auto r = LexOne("'X ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralLexing, UnbasedUnsizedUpperZ) {
  auto r = LexOne("'Z ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralLexing, NoDigitsAfterBaseError) {
  auto [tokens, errors] = LexWithDiag("8'd-6");
  EXPECT_TRUE(errors);
}

TEST(IntegerLiteralLexing, DecimalXZMixedError) {
  auto [tokens, errors] = LexWithDiag("8'd1x");
  EXPECT_TRUE(errors);
}

TEST(IntegerLiteralLexing, DecimalXZMultiError) {
  auto [tokens, errors] = LexWithDiag("8'dxz");
  EXPECT_TRUE(errors);
}

TEST(IntegerLiteralLexing, HexDigitsCaseInsensitive) {
  auto r1 = LexOne("8'habcd ");
  auto r2 = LexOne("8'hABCD ");
  EXPECT_EQ(r1.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r2.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, LargeUnsizedHex) {
  auto r = LexOne("'h7_0000_0000 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, IntegerLiteralRecognized) {
  auto r = LexOne("32'd100");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, UnbasedUnsizedLiteralRecognized) {
  auto r = LexOne("'1");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralLexing, SpaceBreaksNumberIntoTwo) {
  auto tokens = Lex("12 34");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

}  // namespace
