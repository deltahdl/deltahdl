#include <gtest/gtest.h>

#include <string>

#include "lexer/string_escape.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_9_1_EscapeNewline) {
  EXPECT_EQ(InterpretStringEscapes(R"(\n)"), "\n");
}

TEST(LexerClause05, Cl5_9_1_EscapeTab) {
  EXPECT_EQ(InterpretStringEscapes(R"(\t)"), "\t");
}

TEST(LexerClause05, Cl5_9_1_EscapeBackslash) {
  EXPECT_EQ(InterpretStringEscapes(R"(\\)"), "\\");
}

TEST(LexerClause05, Cl5_9_1_EscapeDoubleQuote) {
  EXPECT_EQ(InterpretStringEscapes(R"(\")"), "\"");
}

TEST(LexerClause05, Cl5_9_1_EscapeVerticalTab) {
  EXPECT_EQ(InterpretStringEscapes(R"(\v)"), "\v");
}

TEST(LexerClause05, Cl5_9_1_EscapeFormFeed) {
  EXPECT_EQ(InterpretStringEscapes(R"(\f)"), "\f");
}

TEST(LexerClause05, Cl5_9_1_EscapeBell) {
  EXPECT_EQ(InterpretStringEscapes(R"(\a)"), "\a");
}

TEST(LexerClause05, Cl5_9_1_OctalThreeDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\101)"), "A");
}

TEST(LexerClause05, Cl5_9_1_OctalTwoDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\11)"), "\t");
}

TEST(LexerClause05, Cl5_9_1_OctalOneDigit) {
  EXPECT_EQ(InterpretStringEscapes(R"(\7)"), "\a");
}

TEST(LexerClause05, Cl5_9_1_OctalMaxDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\1019)"), "A9");
}

TEST(LexerClause05, Cl5_9_1_OctalZero) {
  std::string expected(1, '\0');
  EXPECT_EQ(InterpretStringEscapes(R"(\0)"), expected);
}

TEST(LexerClause05, Cl5_9_1_HexTwoDigits) {
  EXPECT_EQ(InterpretStringEscapes(R"(\x41)"), "A");
}

TEST(LexerClause05, Cl5_9_1_HexOneDigit) {
  EXPECT_EQ(InterpretStringEscapes(R"(\xA)"), "\n");
}

TEST(LexerClause05, Cl5_9_1_HexUpperCase) {
  EXPECT_EQ(InterpretStringEscapes(R"(\xFF)"), "\xFF");
}

TEST(LexerClause05, Cl5_9_1_HexLowerCase) {
  EXPECT_EQ(InterpretStringEscapes(R"(\xff)"), "\xFF");
}

TEST(LexerClause05, Cl5_9_1_UnknownEscapeDropsBackslash) {
  EXPECT_EQ(InterpretStringEscapes(R"(\b)"), "b");
}

TEST(LexerClause05, Cl5_9_1_LineContinuation) {
  EXPECT_EQ(InterpretStringEscapes("\\\n"), "");
}

TEST(LexerClause05, Cl5_9_1_MultipleEscapes) {
  EXPECT_EQ(InterpretStringEscapes(R"(A\nB\tC)"), "A\nB\tC");
}

TEST(LexerClause05, Cl5_9_1_MixedEscapeTypes) {
  EXPECT_EQ(InterpretStringEscapes(R"(\x41\101\n)"), "AA\n");
}

}  // namespace
