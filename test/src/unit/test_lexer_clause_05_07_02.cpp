#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_7_2_FixedPoint) {
  auto r = LexOne("14.72 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "14.72");
}

TEST(LexerClause05, Cl5_7_2_ZeroPointOne) {
  auto r = LexOne("0.1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "0.1");
}

TEST(LexerClause05, Cl5_7_2_LargeFixedPoint) {
  auto r = LexOne("2394.26331 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "2394.26331");
}

TEST(LexerClause05, Cl5_7_2_ScientificUpperE) {
  auto r = LexOne("1.2E12 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1.2E12");
}

TEST(LexerClause05, Cl5_7_2_ScientificLowerE) {
  auto r = LexOne("1.30e-2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1.30e-2");
}

TEST(LexerClause05, Cl5_7_2_ScientificZeroExp) {
  auto r = LexOne("0.1e-0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "0.1e-0");
}

TEST(LexerClause05, Cl5_7_2_ExponentOnlyUpperE) {
  auto r = LexOne("23E10 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "23E10");
}

TEST(LexerClause05, Cl5_7_2_ExponentOnlyNegative) {
  auto r = LexOne("29E-2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "29E-2");
}

TEST(LexerClause05, Cl5_7_2_ExponentPositiveSign) {
  auto r = LexOne("1.0e+2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "1.0e+2");
}

TEST(LexerClause05, Cl5_7_2_UnderscoresInReal) {
  auto r = LexOne("236.123_763_e-12 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

TEST(LexerClause05, Cl5_7_2_UnderscoresInIntegerPart) {
  auto r = LexOne("1_000.000_1 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

TEST(LexerClause05, Cl5_7_2_IntegerWithExponent) {
  auto r = LexOne("39e8 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
  EXPECT_EQ(r.token.text, "39e8");
}

TEST(LexerClause05, Cl5_7_2_IntegerExponentE) {
  auto r = LexOne("1e3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

}
