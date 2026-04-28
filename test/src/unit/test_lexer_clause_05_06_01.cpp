#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, BasicEscapedIdentifier) {
  auto r = LexOne("\\cpu3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "cpu3");
}

TEST(LexicalConventionLexing, TerminatedBySpace) {
  auto tokens = Lex("\\esc_id next");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "esc_id");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "next");
}

TEST(LexicalConventionLexing, SpecialCharsInEscaped) {
  auto r = LexOne("\\***error-condition*** ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "***error-condition***");
}

TEST(LexicalConventionLexing, ForwardSlash) {
  auto r = LexOne("\\net1/\\net2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "net1/\\net2");
}

TEST(LexicalConventionLexing, Braces) {
  auto r = LexOne("\\{a,b} ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "{a,b}");
}

TEST(LexicalConventionLexing, PlusSign) {
  auto r = LexOne("\\busa+index ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "busa+index");
}

TEST(LexicalConventionLexing, EscapedKeywordIsIdentifier) {
  auto r = LexOne("\\module ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_NE(r.token.kind, TokenKind::kKwModule);
}

TEST(LexicalConventionLexing, EscapedBeginIsIdentifier) {
  auto r = LexOne("\\begin ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
}

TEST(LexicalConventionLexing, MaxLengthOk) {
  std::string id = "\\" + std::string(1023, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
}

TEST(LexicalConventionLexing, MultipleEscapedInSequence) {
  auto tokens = Lex("\\abc \\def \\ghi ");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[2].text, "ghi");
}

TEST(LexicalConventionLexing, DashClock) {
  auto r = LexOne("\\-clock ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "-clock");
}

TEST(LexicalConventionLexing, ParenthesesInEscaped) {
  auto r = LexOne("\\a*(b+c) ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "a*(b+c)");
}

TEST(LexicalConventionLexing, MinPrintableAsciiChar) {
  auto r = LexOne("\\! ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "!");
}

TEST(LexicalConventionLexing, MaxPrintableAsciiChar) {
  auto r = LexOne("\\~ ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "~");
}

TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByNewline) {
  auto tokens = Lex("\\abc\ndef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
}

TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByTab) {
  auto tokens = Lex("\\abc\tdef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, EscapedIdentifierAtEof) {
  auto tokens = Lex("\\abc");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByFormfeed) {
  auto tokens = Lex("\\abc\fdef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
}

TEST(LexicalConventionLexing, EscapedAndSimpleIdentLexToSameText) {
  auto escaped = LexOne("\\cpu3 ");
  auto simple = LexOne("cpu3");
  EXPECT_EQ(escaped.token.text, simple.token.text);
  EXPECT_EQ(escaped.token.text, "cpu3");
}

// §5.6.1: white space terminator covers carriage return.
TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByCarriageReturn) {
  auto tokens = Lex("\\abc\rdef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
}

// §5.6.1: escaped body may begin with a digit (simple identifiers cannot).
TEST(LexicalConventionLexing, EscapedIdentifierStartingWithDigit) {
  auto r = LexOne("\\1234 ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "1234");
}

// §5.6.1: lexer preserves case of body characters verbatim.
TEST(LexicalConventionLexing, EscapedIdentifierPreservesCase) {
  auto r = LexOne("\\AbCdEf ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "AbCdEf");
}

}  // namespace
