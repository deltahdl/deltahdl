#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "lexer/string_escape.h"

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

TEST(LexicalConventionLexing, LineContinuation) {
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

// An x or z (which are legal digits in numeric literals) is never accepted as a
// digit of an octal escape, so it ends the octal run and stands as its own
// character instead.
TEST(LexicalConventionLexing, OctalEscapeExcludesXAndZDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\1x)"), std::string("\x01") + "x");
  EXPECT_EQ(InterpretStringEscapes(R"(\1z)"), std::string("\x01") + "z");
}

// Likewise, an x or z is never accepted as a digit of a hex escape; it ends the
// hex run and remains a literal character.
TEST(LexicalConventionLexing, HexEscapeExcludesXAndZDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\x1x)"), std::string("\x01") + "x");
  EXPECT_EQ(InterpretStringEscapes(R"(\x1z)"), std::string("\x01") + "z");
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
