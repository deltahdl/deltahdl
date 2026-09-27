#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

using namespace delta;

namespace {

// §5.9.1's escapes are decoded where a string literal's value is formed, in
// src/simulator/evaluation_literal.cpp, and test_simulator_subclause_05_09_01
// checks each of them there. What is left to the lexer is to take the escapes
// as part of one string literal token and to reject the digits Table 5-1 makes
// illegal in one, which is what the cases here check.

TEST(LexicalConventionLexing, StringWithEscapeSequences) {
  auto r = LexOne("\"line1\\nline2\" ");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

// Triple-quoted literals accept unescaped " and newline characters, but the
// escape sequences for those characters remain valid inside them too: an
// escaped " does not end the literal.
TEST(LexicalConventionLexing, TripleQuotedEscapeSequencesSupported) {
  auto r = LexOne(R"("""a\nb\"c""")");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, R"("""a\nb\"c""")");
}

// Table 5-1 makes it illegal for a digit of an octal escape to be an x_digit
// or a z_digit, and an escape of fewer than three digits may not be followed
// by an octal_digit, which Syntax 5-2 has include x, X, z, Z and ?. The lexer
// reports the sequence where the string is lexed, so the design is rejected
// rather than printing the character and then the letter.
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

// Likewise for a hex escape: its digits are hex_digits, which include the x
// and z digits, and those are illegal in an escape.
TEST(LexicalConventionLexing, HexEscapeWithXDigitIsRejected) {
  auto diags = LexDiagnostics("\"\\x4x\"");
  EXPECT_TRUE(ReportedError(diags, "hex escape", 1, "5.9.1"));
}

TEST(LexicalConventionLexing, HexEscapeWhoseFirstDigitIsZIsRejected) {
  auto diags = LexDiagnostics("\"\\xZ\"");
  EXPECT_TRUE(ReportedError(diags, "hex escape", 1, "5.9.1"));
}

// The report names the line the escape is on, which in a triple-quoted
// literal spanning lines is not the line the literal opens on.
TEST(LexicalConventionLexing, TripleQuotedEscapeWithZDigitIsRejectedOnItsLine) {
  auto diags = LexDiagnostics("\"\"\"a\n\\1z\"\"\"");
  EXPECT_TRUE(ReportedError(diags, "octal escape", 2, "5.9.1"));
}

// A full-length escape, an escape followed by a character that is not a digit
// of its kind, and an escape that ends the string are the legal forms and
// report nothing: three octal digits then a 9, two hex digits, one hex digit
// then a g, and one octal digit then the closing quote.
TEST(LexicalConventionLexing, LegalNumericEscapesReportNothing) {
  EXPECT_TRUE(LexDiagnostics("\"\\1019\"").empty());
  EXPECT_TRUE(LexDiagnostics("\"\\x41\"").empty());
  EXPECT_TRUE(LexDiagnostics("\"\\x4g\"").empty());
  EXPECT_TRUE(LexDiagnostics("\"\\7\"").empty());
}

// An x after a complete escape is an ordinary character, since the escape
// took every digit it may: \101x is `A` then `x`, and \x41x is the same.
TEST(LexicalConventionLexing, XAfterACompleteNumericEscapeIsACharacter) {
  EXPECT_TRUE(LexDiagnostics("\"\\101x\"").empty());
  EXPECT_TRUE(LexDiagnostics("\"\\x41x\"").empty());
}

// The x_digits Syntax 5-2 lists include the capital X, which is as illegal
// after a short octal escape as the lowercase one.
TEST(LexicalConventionLexing, OctalEscapeWithCapitalXDigitIsRejected) {
  auto diags = LexDiagnostics("\"\\1X\"");
  EXPECT_TRUE(ReportedError(diags, "octal escape", 1, "5.9.1"));
}

}  // namespace
