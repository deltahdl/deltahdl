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

}  // namespace
