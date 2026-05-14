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

// §A.8.7: octal_digit — x_digit | z_digit | 0..7

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

// §A.8.7: hex_digit — x_digit | z_digit | 0..9 | a..f | A..F

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

// §A.8.7: decimal_number/binary_number/octal_number/hex_number — the
// [size] prefix is optional, so the signed-base form `'[s|S]<base>` is
// itself a valid number with no leading size.

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

// §A.8.7: size ::= unsigned_number, and unsigned_number permits underscores
// between digits — the size prefix may therefore contain `_`.
TEST(NumberTokenLexing, SizeWithUnderscoreDigits) {
  auto r = LexOne("1_2'b0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "1_2'b0");
}

// §A.8.7: decimal_number's x_digit and z_digit forms are
// `[ size ] decimal_base x_digit { _ }` and the z_digit equivalent —
// trailing underscores after the lone x_digit or z_digit are permitted.
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

// §A.8.7: real_number — exp [ sign ] unsigned_number; the unsigned_number
// after the exponent marker must start with decimal_digit, so a bare
// 'e'/'E' (no digit) must not extend the integer into a real literal.

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

// §A.8.7: error — invalid digits for base

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

// §A.8.7: unbased_unsized_literal is a single contiguous token —
// `'0`/`'1`/`'z_or_x` with no whitespace allowed between the apostrophe
// and the value character.
TEST(NumberTokenLexing, WhitespaceAfterApostropheNotUnbasedUnsized) {
  auto tokens = Lex("' 1 ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_NE(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

// §A.8.7: hex_value ::= hex_digit { _ | hex_digit } — an underscore at the
// first position of the value is rejected (the value must start with a
// hex_digit). Covers the hex base; the binary base is covered by
// ErrorUnderscoreLeadingDigitValue above.
TEST(NumberTokenLexing, ErrorUnderscoreLeadingDigitValueHex) {
  auto [tokens, errors] = LexWithDiag("8'h_FF ");
  EXPECT_TRUE(errors);
}

// §A.8.7: decimal_number with x_digit/z_digit — the BNF only allows
// `[ size ] decimal_base x_digit { _ }` or `[ size ] decimal_base z_digit { _ }`,
// so an x/z digit must be the sole value digit and may not be mixed with
// regular decimal digits or another x/z digit.
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

// §A.8.7: binary_digit ::= x_digit | z_digit | 0 | 1, with z_digit ::= z | Z | ?.
// Covers the binary base path for `?`.
TEST(NumberTokenLexing, BinaryValueWithQuestion) {
  auto r = LexOne("4'b? ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

// §A.8.7: fixed_point_number ::= unsigned_number . unsigned_number — the
// production requires an unsigned_number on both sides of the dot. A bare
// leading or trailing dot must not extend the integer into a real literal,
// and a dot without fractional digits before the exponent marker likewise
// must not.
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

// §A.8.7: unsigned_number ::= decimal_digit { _ | decimal_digit } — a
// trailing underscore is allowed inside an unsigned_number, including
// immediately before the exponent marker.
TEST(NumberTokenLexing, RealTrailingUnderscoreBeforeExponent) {
  auto r = LexOne("236.123_763_e-12 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

}  // namespace
