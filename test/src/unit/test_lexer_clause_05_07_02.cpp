#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(RealLiteralLexing, FixedPoint) {
  auto r = LexOne("14.72 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "14.72");
}

TEST(RealLiteralLexing, ZeroPointOne) {
  auto r = LexOne("0.1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "0.1");
}

TEST(RealLiteralLexing, LargeFixedPoint) {
  auto r = LexOne("2394.26331 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "2394.26331");
}

TEST(RealLiteralLexing, ScientificUpperE) {
  auto r = LexOne("1.2E12 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1.2E12");
}

TEST(RealLiteralLexing, ScientificLowerE) {
  auto r = LexOne("1.30e-2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1.30e-2");
}

TEST(RealLiteralLexing, ScientificZeroExp) {
  auto r = LexOne("0.1e-0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "0.1e-0");
}

TEST(RealLiteralLexing, ExponentOnlyUpperE) {
  auto r = LexOne("23E10 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "23E10");
}

TEST(RealLiteralLexing, ExponentOnlyNegative) {
  auto r = LexOne("29E-2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "29E-2");
}

TEST(RealLiteralLexing, ExponentPositiveSign) {
  auto r = LexOne("1.0e+2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1.0e+2");
}

TEST(RealLiteralLexing, UnderscoresInReal) {
  auto r = LexOne("236.123_763_e-12 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

TEST(RealLiteralLexing, UnderscoresInIntegerPart) {
  auto r = LexOne("1_000.000_1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

TEST(RealLiteralLexing, IntegerWithExponent) {
  auto r = LexOne("39e8 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "39e8");
}

TEST(RealLiteralLexing, IntegerExponentE) {
  auto r = LexOne("1e3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

TEST(RealLiteralLexing, RealLiteralRecognized) {
  auto r = LexOne("3.14");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

TEST(RealLiteralLexing, LeadingDotNotRealLiteral) {
  auto tokens = Lex(".12 ");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(RealLiteralLexing, TrailingDotNotRealLiteral) {
  auto tokens = Lex("9.; ");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "9");
}

TEST(RealLiteralLexing, DotBeforeExponentNotRealLiteral) {
  auto tokens = Lex("4.E3 ");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "4");
}

TEST(RealLiteralLexing, LeadingDotWithExponentNotRealLiteral) {
  auto tokens = Lex(".2e-7 ");
  EXPECT_EQ(tokens[0].kind, TokenKind::kDot);
}

}  // namespace
