#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §5.7.2: real numbers may be written in decimal (fixed-point) notation, with a
// digit present on each side of the decimal point. Such a form lexes as a
// single real literal token.
TEST(RealLiteralLexing, DecimalNotationIsRealLiteral) {
  auto r = LexOne("14.72 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "14.72");
}

TEST(RealLiteralLexing, LeadingZeroDecimalIsRealLiteral) {
  auto r = LexOne("0.1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "0.1");
}

// §5.7.2: real numbers may also be written in scientific notation, including
// the exponent-only form (e.g. 39e8 = 39 x 10^8).
TEST(RealLiteralLexing, ExponentOnlyIsRealLiteral) {
  auto r = LexOne("39e8 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "39e8");
}

TEST(RealLiteralLexing, FixedPointWithExponentIsRealLiteral) {
  auto r = LexOne("1.30e-2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1.30e-2");
}

// §5.7.2: a real number expressed with a decimal point shall have at least one
// digit on each side of the point. The four forms below are the standard's own
// list of invalid real numbers; the lexer must not accept any of them as a
// single real literal token.

// No digit before the point: the point is a separate token, not the start of a
// real literal.
TEST(RealLiteralLexing, NoLeadingDigitIsNotRealLiteral) {
  auto tokens = Lex(".12 ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_NE(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDot);
}

// No digit after the point: the point is left unconsumed, so the digits ahead
// of it lex as an integer literal rather than a real literal.
TEST(RealLiteralLexing, NoTrailingDigitIsNotRealLiteral) {
  auto tokens = Lex("9. ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "9");
}

// A point with an exponent but no fractional digit is still missing the digit
// after the point, so it is not a real literal.
TEST(RealLiteralLexing, PointBeforeExponentIsNotRealLiteral) {
  auto tokens = Lex("4.E3 ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "4");
}

// Missing the digit before the point, even with an exponent, is not a real
// literal.
TEST(RealLiteralLexing, NoLeadingDigitWithExponentIsNotRealLiteral) {
  auto tokens = Lex(".2e-7 ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_NE(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDot);
}

}  // namespace
