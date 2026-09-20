#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

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

// §5.7.2 has a real number written with a decimal point carry a digit on each
// side of the point, and lists the four forms below as invalid for lacking
// one. The lexer reads each as the one real literal it was written to be, so
// that the statement holding it is parsed in step, and reports the spelling
// under §5.7.2 naming the side that has no digit. The tests are one per form
// so that a failure names the form.

// No digit before the point.
TEST(RealLiteralLexing, NoLeadingDigitIsReportedUnderClause572) {
  EXPECT_TRUE(ReportedError(
      LexDiagnostics(".12 "),
      "real literal '.12' has no digit before its decimal point", 1, "5.7.2"));
  auto tokens = Lex(".12 ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, ".12");
}

// No digit after the point.
TEST(RealLiteralLexing, NoTrailingDigitIsReportedUnderClause572) {
  EXPECT_TRUE(ReportedError(
      LexDiagnostics("9. "),
      "real literal '9.' has no digit after its decimal point", 1, "5.7.2"));
  auto tokens = Lex("9. ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "9.");
}

// A point with an exponent but no fractional digit is still missing the digit
// after the point; the exponent is read with the literal.
TEST(RealLiteralLexing, PointBeforeExponentIsReportedUnderClause572) {
  EXPECT_TRUE(ReportedError(
      LexDiagnostics("4.E3 "),
      "real literal '4.E3' has no digit after its decimal point", 1, "5.7.2"));
  auto tokens = Lex("4.E3 ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "4.E3");
}

// Missing the digit before the point, even with an exponent.
TEST(RealLiteralLexing, NoLeadingDigitWithExponentIsReportedUnderClause572) {
  EXPECT_TRUE(ReportedError(
      LexDiagnostics(".2e-7 "),
      "real literal '.2e-7' has no digit before its decimal point", 1,
      "5.7.2"));
  auto tokens = Lex(".2e-7 ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, ".2e-7");
}

// The legal spellings of §5.7.2's own list, with a digit on each side of the
// point or no point at all, draw nothing: the report is for the point that
// lacks a digit, not for the point or the exponent as such.
TEST(RealLiteralLexing, DigitsOnBothSidesOfThePointDrawNoClause572Report) {
  EXPECT_TRUE(LexDiagnostics("0.1 ").empty());
  EXPECT_TRUE(LexDiagnostics("1.2E12 ").empty());
  EXPECT_TRUE(LexDiagnostics("29E-2 ").empty());
}

}  // namespace
