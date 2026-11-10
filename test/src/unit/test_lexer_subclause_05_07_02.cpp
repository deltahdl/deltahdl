#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

using namespace delta;

namespace {

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

TEST(RealLiteralLexing, NoLeadingDigitIsReported) {
  EXPECT_TRUE(ReportedError(
      LexDiagnostics(".12 "),
      "real literal '.12' has no digit before its decimal point", 1, "5.7.2"));
  auto tokens = Lex(".12 ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, ".12");
}

TEST(RealLiteralLexing, NoTrailingDigitIsReported) {
  EXPECT_TRUE(ReportedError(
      LexDiagnostics("9. "),
      "real literal '9.' has no digit after its decimal point", 1, "5.7.2"));
  auto tokens = Lex("9. ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "9.");
}

TEST(RealLiteralLexing, PointBeforeExponentIsReported) {
  EXPECT_TRUE(ReportedError(
      LexDiagnostics("4.E3 "),
      "real literal '4.E3' has no digit after its decimal point", 1, "5.7.2"));
  auto tokens = Lex("4.E3 ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "4.E3");
}

TEST(RealLiteralLexing, NoLeadingDigitWithExponentIsReported) {
  EXPECT_TRUE(ReportedError(
      LexDiagnostics(".2e-7 "),
      "real literal '.2e-7' has no digit before its decimal point", 1,
      "5.7.2"));
  auto tokens = Lex(".2e-7 ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, ".2e-7");
}

TEST(RealLiteralLexing, DigitsOnBothSidesOfThePointDrawNoReport) {
  EXPECT_TRUE(LexDiagnostics("0.1 ").empty());
  EXPECT_TRUE(LexDiagnostics("1.2E12 ").empty());
  EXPECT_TRUE(LexDiagnostics("29E-2 ").empty());
}

TEST(RealLiteralLexing, UnderscoresAmongExponentAndFractionDigits) {
  auto exponent = Lex("1e1_0");
  ASSERT_EQ(exponent.size(), 2u);
  EXPECT_EQ(exponent[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(exponent[0].text, "1e1_0");

  auto no_leading_digit = Lex(".1_2");
  ASSERT_EQ(no_leading_digit.size(), 2u);
  EXPECT_EQ(no_leading_digit[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(no_leading_digit[0].text, ".1_2");
  EXPECT_TRUE(
      ReportedError(LexDiagnostics(".1_2"), "no digit before", 1, "5.7.2"));
}

TEST(RealLiteralLexing, WhiteSpaceInsideARealLiteralSplitsIt) {
  auto whole = Lex("1.5e3 ");
  ASSERT_EQ(whole.size(), 2u);
  EXPECT_EQ(whole[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(whole[0].text, "1.5e3");

  auto before_exponent = Lex("1.5 e3 ");
  ASSERT_EQ(before_exponent.size(), 3u);
  EXPECT_EQ(before_exponent[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(before_exponent[0].text, "1.5");
  EXPECT_EQ(before_exponent[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(before_exponent[1].text, "e3");

  auto inside_exponent = Lex("1.5e 3 ");
  ASSERT_EQ(inside_exponent.size(), 4u);
  EXPECT_EQ(inside_exponent[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(inside_exponent[0].text, "1.5");
  EXPECT_EQ(inside_exponent[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(inside_exponent[1].text, "e");
  EXPECT_EQ(inside_exponent[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(inside_exponent[2].text, "3");

  EXPECT_TRUE(
      ReportedError(LexDiagnostics("1 .5 "), "no digit before", 1, "5.7.2"));
  EXPECT_TRUE(
      ReportedError(LexDiagnostics("1. 5 "), "no digit after", 1, "5.7.2"));
}

TEST(RealLiteralLexing, UnderscoreOpeningTheFractionIsReported) {
  EXPECT_TRUE(
      ReportedError(LexDiagnostics("1._5 "), "no digit after", 1, "5.7.2"));
  EXPECT_TRUE(LexDiagnostics("1_.5_ ").empty());
  auto trailing = Lex("1_.5_e3 ");
  ASSERT_EQ(trailing.size(), 2u);
  EXPECT_EQ(trailing[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(trailing[0].text, "1_.5_e3");
}

}  // namespace
