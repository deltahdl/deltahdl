#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §A.8.7: unsigned_number — decimal_digit { _ | decimal_digit }

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

// §A.8.7: decimal_number — [size] decimal_base unsigned_number

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

// §A.8.7: decimal_number — [size] decimal_base x_digit { _ }

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

// §A.8.7: decimal_number — [size] decimal_base z_digit { _ }

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

// §A.8.7: binary_number — [size] binary_base binary_value

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

// §A.8.7: octal_number — [size] octal_base octal_value

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

// §A.8.7: hex_number — [size] hex_base hex_value

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

// §A.8.7: signed bases — 'sd, 'sb, 'so, 'sh

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

// §A.8.7: real_number — fixed_point_number

TEST(NumberTokenLexing, FixedPointNumber) {
  auto r = LexOne("3.14 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "3.14");
}

// §A.8.7: real_number — unsigned_number [. unsigned_number] exp [sign] unsigned_number

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

// §A.8.7: unbased_unsized_literal — '0 | '1 | 'z_or_x

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

// §A.8.7: error — invalid digits for base

TEST(NumberTokenLexing, ErrorBinaryDigitOutOfRange) {
  auto [tokens, errors] = LexWithDiag("4'b2 ");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, ErrorOctalDigitOutOfRange) {
  auto [tokens, errors] = LexWithDiag("4'o8 ");
  EXPECT_TRUE(errors);
}

TEST(NumberTokenLexing, ErrorUnderscoreLeadingDigitValue) {
  auto [tokens, errors] = LexWithDiag("4'b_1 ");
  EXPECT_TRUE(errors);
}

}  // namespace
