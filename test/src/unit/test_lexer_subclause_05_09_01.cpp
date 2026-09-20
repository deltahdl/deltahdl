#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/string_escape.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, EscapeNewline) {
  EXPECT_EQ(InterpretStringEscapes(R"(\n)"), "\n");
}

TEST(LexicalConventionLexing, EscapeTab) {
  EXPECT_EQ(InterpretStringEscapes(R"(\t)"), "\t");
}

TEST(LexicalConventionLexing, EscapeBackslash) {
  EXPECT_EQ(InterpretStringEscapes(R"(\\)"), "\\");
}

TEST(LexicalConventionLexing, EscapeDoubleQuote) {
  EXPECT_EQ(InterpretStringEscapes(R"(\")"), "\"");
}

TEST(LexicalConventionLexing, EscapeVerticalTab) {
  EXPECT_EQ(InterpretStringEscapes(R"(\v)"), "\v");
}

TEST(LexicalConventionLexing, EscapeFormFeed) {
  EXPECT_EQ(InterpretStringEscapes(R"(\f)"), "\f");
}

TEST(LexicalConventionLexing, EscapeBell) {
  EXPECT_EQ(InterpretStringEscapes(R"(\a)"), "\a");
}

TEST(LexicalConventionLexing, OctalThreeDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\101)"), "A");
}

TEST(LexicalConventionLexing, OctalTwoDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\11)"), "\t");
}

TEST(LexicalConventionLexing, OctalOneDigit) {
  EXPECT_EQ(InterpretStringEscapes(R"(\7)"), "\a");
}

TEST(LexicalConventionLexing, OctalMaxDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\1019)"), "A9");
}

TEST(LexicalConventionLexing, OctalZero) {
  std::string expected(1, '\0');
  EXPECT_EQ(InterpretStringEscapes(R"(\0)"), expected);
}

TEST(LexicalConventionLexing, HexTwoDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\x41)"), "A");
}

TEST(LexicalConventionLexing, HexOneDigit) {
  EXPECT_EQ(InterpretStringEscapes(R"(\xA)"), "\n");
}

TEST(LexicalConventionLexing, HexUpperCase) {
  EXPECT_EQ(InterpretStringEscapes(R"(\xFF)"), "\xFF");
}

TEST(LexicalConventionLexing, HexLowerCase) {
  EXPECT_EQ(InterpretStringEscapes(R"(\xff)"), "\xFF");
}

TEST(LexicalConventionLexing, UnknownEscapeDropsBackslash) {
  EXPECT_EQ(InterpretStringEscapes(R"(\b)"), "b");
}

// In a line continuation sequence both the backslash and the newline character
// are ignored, so interpreting the escapes of that sequence alone produces no
// characters at all. That such a sequence still lexes as a single string
// literal token is covered in the sibling file.
TEST(LexicalConventionLexing, LineContinuationSequenceIgnored) {
  EXPECT_EQ(InterpretStringEscapes("\\\n"), "");
}

TEST(LexicalConventionLexing, MultipleEscapes) {
  EXPECT_EQ(InterpretStringEscapes(R"(A\nB\tC)"), "A\nB\tC");
}

TEST(LexicalConventionLexing, MixedEscapeTypes) {
  EXPECT_EQ(InterpretStringEscapes(R"(\x41\101\n)"), "AA\n");
}

TEST(LexicalConventionLexing, LineContinuationCrLf) {
  EXPECT_EQ(InterpretStringEscapes("\\\r\n"), "");
}

TEST(LexicalConventionLexing, OctalMaxValid) {
  EXPECT_EQ(InterpretStringEscapes(R"(\377)"), "\xFF");
}

TEST(LexicalConventionLexing, StringWithEscapeSequences) {
  auto r = LexOne("\"line1\\nline2\" ");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

// A double backslash immediately before a newline is the escape for a single
// backslash, so the newline is preserved as a literal rather than swallowed as
// a line continuation.
TEST(LexicalConventionLexing, DoubleBackslashBeforeNewlineIsNotContinuation) {
  EXPECT_EQ(InterpretStringEscapes("\\\\\n"), "\\\n");
}

// Because the double backslash binds first, a line continuation that survives a
// trailing backslash needs a third backslash: \\\<newline> yields one
// backslash with the newline consumed as the continuation.
TEST(LexicalConventionLexing, LineContinuationRequiresThirdBackslash) {
  EXPECT_EQ(InterpretStringEscapes("\\\\\\\n"), "\\");
}

// Triple-quoted literals accept unescaped " and newline characters, but the
// escape sequences for those characters remain valid inside them too.
TEST(LexicalConventionLexing, TripleQuotedEscapeSequencesSupported) {
  auto r = LexOne(R"("""a\nb\"c""")");
  ASSERT_EQ(r.token.kind, TokenKind::kStringLiteral);
  std::string body =
      std::string(r.token.text).substr(3, r.token.text.size() - 6);
  EXPECT_EQ(InterpretStringEscapes(body), "a\nb\"c");
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
  EXPECT_EQ(InterpretStringEscapes(R"(\101x)"), "Ax");
  EXPECT_EQ(InterpretStringEscapes(R"(\x41x)"), "Ax");
}

// A hex escape consumes at most two hex digits, so a third hex digit stands as
// its own character: \x411 is the byte 0x41 followed by a literal '1'.
TEST(LexicalConventionLexing, HexConsumesAtMostTwoDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\x411)"), "A1");
}

// An octal escape consumes at most three digits even when the following
// character is itself an octal digit, which is how the ambiguity of a short
// octal run is resolved: \1011 is the byte 0101 ('A') then a literal '1'.
TEST(LexicalConventionLexing, OctalConsumesAtMostThreeDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\1011)"), "A1");
}

}  // namespace
