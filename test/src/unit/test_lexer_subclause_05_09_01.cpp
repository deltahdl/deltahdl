#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, StringWithEscapeSequences) {
  auto r = LexOne("\"line1\\nline2\" ");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, TripleQuotedEscapeSequencesSupported) {
  auto r = LexOne(R"("""a\nb\"c""")");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, R"("""a\nb\"c""")");
}

TEST(LexicalConventionLexing, OctalEscapeWithZDigitIsRejected) {
  auto diags = LexDiagnostics("\"\\1z\"");
  EXPECT_TRUE(ReportedError(diags, "octal escape", 1, "5.9.1"));
}

TEST(LexicalConventionLexing, OctalEscapeWithQuestionMarkDigitIsRejected) {
  auto diags = LexDiagnostics("\"\\1?\"");
  EXPECT_TRUE(ReportedError(diags, "octal escape", 1, "5.9.1"));
}

TEST(LexicalConventionLexing, TwoDigitOctalEscapeWithXDigitIsRejected) {
  auto diags = LexDiagnostics("\"\\77x\"");
  EXPECT_TRUE(ReportedError(diags, "octal escape", 1, "5.9.1"));
}

TEST(LexicalConventionLexing, HexEscapeWithXDigitIsRejected) {
  auto diags = LexDiagnostics("\"\\x4x\"");
  EXPECT_TRUE(ReportedError(diags, "hex escape", 1, "5.9.1"));
}

TEST(LexicalConventionLexing, HexEscapeWhoseFirstDigitIsZIsRejected) {
  auto diags = LexDiagnostics("\"\\xZ\"");
  EXPECT_TRUE(ReportedError(diags, "hex escape", 1, "5.9.1"));
}

TEST(LexicalConventionLexing, TripleQuotedEscapeWithZDigitIsRejectedOnItsLine) {
  auto diags = LexDiagnostics("\"\"\"a\n\\1z\"\"\"");
  EXPECT_TRUE(ReportedError(diags, "octal escape", 2, "5.9.1"));
}

TEST(LexicalConventionLexing, LegalNumericEscapesReportNothing) {
  EXPECT_TRUE(LexDiagnostics("\"\\1019\"").empty());
  EXPECT_TRUE(LexDiagnostics("\"\\x41\"").empty());
  EXPECT_TRUE(LexDiagnostics("\"\\x4g\"").empty());
  EXPECT_TRUE(LexDiagnostics("\"\\7\"").empty());
}

TEST(LexicalConventionLexing, XAfterACompleteNumericEscapeIsACharacter) {
  EXPECT_TRUE(LexDiagnostics("\"\\101x\"").empty());
  EXPECT_TRUE(LexDiagnostics("\"\\x41x\"").empty());
}

TEST(LexicalConventionLexing, OctalEscapeWithCapitalXDigitIsRejected) {
  auto diags = LexDiagnostics("\"\\1X\"");
  EXPECT_TRUE(ReportedError(diags, "octal escape", 1, "5.9.1"));
}

}  // namespace
