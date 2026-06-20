#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NumberTokenLexing, UnsignedNumber) {
  auto r = LexOne("42 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "42");
}

TEST(NumberTokenLexing, UnsignedNumberWithUnderscores) {
  auto r = LexOne("1_000_000 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "1_000_000");
}

TEST(NumberTokenLexing, UnsignedNumberZero) {
  auto r = LexOne("0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "0");
}

TEST(NumberTokenLexing, DecimalBaseUnsized) {
  auto r = LexOne("'d99 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'d99");
}

TEST(NumberTokenLexing, DecimalBaseSized) {
  auto r = LexOne("8'd255 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'd255");
}

TEST(NumberTokenLexing, DecimalBaseUpperD) {
  auto r = LexOne("'D7 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'D7");
}

TEST(NumberTokenLexing, DecimalBaseXDigit) {
  auto r = LexOne("8'dx ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'dx");
}

TEST(NumberTokenLexing, DecimalBaseXDigitUpper) {
  auto r = LexOne("8'dX ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'dX");
}

TEST(NumberTokenLexing, DecimalBaseZDigit) {
  auto r = LexOne("8'dz ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'dz");
}

TEST(NumberTokenLexing, DecimalBaseZDigitUpper) {
  auto r = LexOne("8'dZ ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'dZ");
}

TEST(NumberTokenLexing, DecimalBaseQuestionMark) {
  auto r = LexOne("8'd? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'd?");
}

TEST(NumberTokenLexing, BinaryBaseUnsized) {
  auto r = LexOne("'b1010 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'b1010");
}

TEST(NumberTokenLexing, BinaryBaseSized) {
  auto r = LexOne("4'b1001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'b1001");
}

TEST(NumberTokenLexing, BinaryBaseUpperB) {
  auto r = LexOne("4'B0110 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'B0110");
}

TEST(NumberTokenLexing, BinaryValueWithUnderscore) {
  auto r = LexOne("8'b1010_0101 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'b1010_0101");
}

TEST(NumberTokenLexing, BinaryValueWithXZ) {
  auto r = LexOne("4'b1xz0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'b1xz0");
}

TEST(NumberTokenLexing, OctalBaseUnsized) {
  auto r = LexOne("'o77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'o77");
}

TEST(NumberTokenLexing, OctalBaseSized) {
  auto r = LexOne("12'o7654 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "12'o7654");
}

TEST(NumberTokenLexing, OctalBaseUpperO) {
  auto r = LexOne("'O70 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'O70");
}

TEST(NumberTokenLexing, OctalValueWithUnderscore) {
  auto r = LexOne("12'o77_77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "12'o77_77");
}

TEST(NumberTokenLexing, OctalValueWithXDigit) {
  auto r = LexOne("8'o7x ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'o7x");
}

TEST(NumberTokenLexing, OctalValueWithZDigit) {
  auto r = LexOne("8'o7Z ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'o7Z");
}

TEST(NumberTokenLexing, OctalValueWithQuestion) {
  auto r = LexOne("8'o? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'o?");
}

TEST(NumberTokenLexing, HexBaseUnsized) {
  auto r = LexOne("'hFF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'hFF");
}

TEST(NumberTokenLexing, HexBaseSized) {
  auto r = LexOne("16'hABCD ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "16'hABCD");
}

TEST(NumberTokenLexing, HexBaseUpperH) {
  auto r = LexOne("'H0F ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'H0F");
}

TEST(NumberTokenLexing, HexValueWithUnderscore) {
  auto r = LexOne("32'hDEAD_BEEF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "32'hDEAD_BEEF");
}

TEST(NumberTokenLexing, HexValueAllDigits) {
  auto r = LexOne("'h0123456789abcdefABCDEF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(NumberTokenLexing, HexValueWithXDigit) {
  auto r = LexOne("8'h1x ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'h1x");
}

TEST(NumberTokenLexing, HexValueWithZDigit) {
  auto r = LexOne("8'h1Z ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'h1Z");
}

TEST(NumberTokenLexing, HexValueWithQuestion) {
  auto r = LexOne("8'h? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'h?");
}

TEST(NumberTokenLexing, SignedDecimalBase) {
  auto r = LexOne("8'sd42 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'sd42");
}

TEST(NumberTokenLexing, SignedBinaryBase) {
  auto r = LexOne("4'sb1010 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'sb1010");
}

TEST(NumberTokenLexing, SignedOctalBase) {
  auto r = LexOne("8'so77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'so77");
}

TEST(NumberTokenLexing, SignedHexBase) {
  auto r = LexOne("8'shFF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'shFF");
}

TEST(NumberTokenLexing, SignedUpperS) {
  auto r = LexOne("4'Sb1010 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'Sb1010");
}

TEST(NumberTokenLexing, UnsizedSignedDecimalBase) {
  auto r = LexOne("'sd42 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'sd42");
}

TEST(NumberTokenLexing, UnsizedSignedBinaryBase) {
  auto r = LexOne("'sb1010 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'sb1010");
}

TEST(NumberTokenLexing, UnsizedSignedOctalBase) {
  auto r = LexOne("'so77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'so77");
}

TEST(NumberTokenLexing, UnsizedSignedHexBase) {
  auto r = LexOne("'shFF ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'shFF");
}

TEST(NumberTokenLexing, SizeWithUnderscoreDigits) {
  auto r = LexOne("1_2'b0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "1_2'b0");
}

TEST(NumberTokenLexing, DecimalBaseXDigitWithTrailingUnderscore) {
  auto r = LexOne("8'dx_ ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'dx_");
}

TEST(NumberTokenLexing, DecimalBaseZDigitWithTrailingUnderscore) {
  auto r = LexOne("8'dz_ ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "8'dz_");
}

TEST(NumberTokenLexing, FixedPointNumber) {
  auto r = LexOne("3.14 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "3.14");
}

TEST(NumberTokenLexing, RealExponentLowerE) {
  auto r = LexOne("1e10 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1e10");
}

TEST(NumberTokenLexing, RealExponentUpperE) {
  auto r = LexOne("1E10 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1E10");
}

TEST(NumberTokenLexing, RealExponentWithNegSign) {
  auto r = LexOne("2.5e-3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "2.5e-3");
}

TEST(NumberTokenLexing, RealExponentWithPosSign) {
  auto r = LexOne("1.0E+6 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1.0E+6");
}

TEST(NumberTokenLexing, RealFixedPointWithUnderscore) {
  auto r = LexOne("1_000.000_1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1_000.000_1");
}

TEST(NumberTokenLexing, UnbasedUnsizedZero) {
  auto r = LexOne("'0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(NumberTokenLexing, UnbasedUnsizedOne) {
  auto r = LexOne("'1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(NumberTokenLexing, UnbasedUnsizedX) {
  auto r = LexOne("'x ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(NumberTokenLexing, UnbasedUnsizedUpperX) {
  auto r = LexOne("'X ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(NumberTokenLexing, UnbasedUnsizedZ) {
  auto r = LexOne("'z ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(NumberTokenLexing, UnbasedUnsizedUpperZ) {
  auto r = LexOne("'Z ");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(NumberTokenLexing, RealExponentBareENotConsumed) {
  auto tokens = Lex("1e ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "e");
}

TEST(NumberTokenLexing, RealExponentBodyNotStartingWithDigit) {
  auto tokens = Lex("1e_5 ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "e_5");
}

TEST(NumberTokenLexing, RealExponentSignWithoutDigit) {
  auto tokens = Lex("1e+ ");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "e");
  EXPECT_EQ(tokens[2].kind, TokenKind::kPlus);
}

TEST(NumberTokenLexing, ErrorBinaryDigitOutOfRange) {
  auto [tokens, errors] = LexWithDiag("4'b2 ");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, ErrorOctalDigitOutOfRange) {
  auto [tokens, errors] = LexWithDiag("4'o8 ");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, ErrorHexDigitOutOfRange) {
  auto [tokens, errors] = LexWithDiag("8'hG ");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, ErrorUnderscoreLeadingDigitValue) {
  auto [tokens, errors] = LexWithDiag("4'b_1 ");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, WhitespaceAfterApostropheNotUnbasedUnsized) {
  auto tokens = Lex("' 1 ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_NE(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(NumberTokenLexing, ErrorUnderscoreLeadingDigitValueHex) {
  auto [tokens, errors] = LexWithDiag("8'h_FF ");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, ErrorDecimalNoValueDigits) {
  auto [tokens, errors] = LexWithDiag("8'd-6");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, ErrorDecimalXZMixedWithDigit) {
  auto [tokens, errors] = LexWithDiag("8'd1x");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, ErrorDecimalMultipleXZDigits) {
  auto [tokens, errors] = LexWithDiag("8'dxz");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, BinaryValueWithQuestion) {
  auto r = LexOne("4'b? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(NumberTokenLexing, RealLeadingDotNotRealLiteral) {
  auto tokens = Lex(".12 ");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(NumberTokenLexing, RealTrailingDotNotRealLiteral) {
  auto tokens = Lex("9.; ");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "9");
}

TEST(NumberTokenLexing, RealDotBeforeExponentNotRealLiteral) {
  auto tokens = Lex("4.E3 ");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "4");
}

TEST(NumberTokenLexing, RealLeadingDotWithExponentNotRealLiteral) {
  auto tokens = Lex(".2e-7 ");
  EXPECT_EQ(tokens[0].kind, TokenKind::kDot);
}

TEST(NumberTokenLexing, RealTrailingUnderscoreBeforeExponent) {
  auto r = LexOne("236.123_763_e-12 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

TEST(NumberTokenLexing, RealExpNoFracPosSign) {
  auto r = LexOne("1e+5 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1e+5");
}

TEST(NumberTokenLexing, RealExpNoFracNegSign) {
  auto r = LexOne("1e-5 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1e-5");
}

TEST(NumberTokenLexing, RealFracExpNoSign) {
  auto r = LexOne("1.5e10 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1.5e10");
}

TEST(NumberTokenLexing, ApostropheQuestionNotUnbasedUnsized) {
  auto tokens = Lex("'? ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_NE(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(NumberTokenLexing, ErrorOctalValueLeadingUnderscore) {
  auto [tokens, errors] = LexWithDiag("8'o_77 ");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, ErrorDecimalValueLeadingUnderscore) {
  auto [tokens, errors] = LexWithDiag("8'd_42 ");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, UnsizedSignedOctalBaseUpperS) {
  auto r = LexOne("'So77 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'So77");
}

TEST(NumberTokenLexing, UnsizedSignedHexBaseUpperS) {
  auto r = LexOne("'Sh1F ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'Sh1F");
}

TEST(NumberTokenLexing, UnsizedSignedDecimalBaseUpperS) {
  auto r = LexOne("'Sd42 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'Sd42");
}

TEST(NumberTokenLexing, UnsizedSignedBinaryBaseUpperS) {
  auto r = LexOne("'Sb1010 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "'Sb1010");
}

TEST(NumberTokenLexing, BinaryValueOnlyXDigit) {
  auto r = LexOne("4'bx ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'bx");
}

TEST(NumberTokenLexing, HexValueOnlyXDigit) {
  auto r = LexOne("4'hx ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'hx");
}

TEST(NumberTokenLexing, OctalValueOnlyXDigit) {
  auto r = LexOne("4'ox ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4'ox");
}

}  // namespace
