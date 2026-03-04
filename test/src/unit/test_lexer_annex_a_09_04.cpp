#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

TEST(LexerA94, SpaceSeparatesTokens) {

  auto tokens = Lex("a b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

TEST(LexerA94, TabSeparatesTokens) {

  auto tokens = Lex("a\tb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, NewlineSeparatesTokens) {

  auto tokens = Lex("a\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, FormfeedSeparatesTokens) {

  auto tokens = Lex("a\fb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, EofTerminatesTokenStream) {

  auto tokens = Lex("a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexerA94, EofOnEmptyInput) {

  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerA94, WhitespaceIgnoredBetweenOperators) {

  auto tokens = Lex("a+b");
  ASSERT_EQ(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].text, "b");
}

TEST(LexerA94, MultipleSpacesIgnored) {

  auto tokens = Lex("a     b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, MixedWhitespaceIgnored) {

  auto tokens = Lex("a \t \n \f b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, LeadingWhitespaceIgnored) {

  auto tokens = Lex("  \t\n  a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(LexerA94, TrailingWhitespaceIgnored) {

  auto tokens = Lex("a  \t\n  ");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexerA94, OnlyWhitespaceInput) {

  auto tokens = Lex("   \t\t\n\n\f  ");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerA94, WhitespaceRequiredBetweenKeywords) {

  auto tokens = Lex("moduleendmodule");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "moduleendmodule");
}

TEST(LexerA94, WhitespaceCorrectlySeparatesKeywords) {

  auto tokens = Lex("module endmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(LexerA94, FormfeedSeparatesKeywords) {

  auto tokens = Lex("module\fendmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(LexerA94, TabSeparatesKeywords) {
  auto tokens = Lex("module\tendmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(LexerA94, NewlineSeparatesKeywords) {
  auto tokens = Lex("module\nendmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(LexerA94, NewlineAdvancesLineNumber) {

  auto [tokens, errors] = LexWithDiag("a\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 2u);
}

TEST(LexerA94, TabAdvancesColumn) {

  auto [tokens, errors] = LexWithDiag("a\tb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.column, 3u);
}

TEST(LexerA94, FormfeedAdvancesColumn) {

  auto [tokens, errors] = LexWithDiag("a\fb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.column, 3u);
}

TEST(LexerA94, MultipleNewlinesTrackCorrectly) {
  auto [tokens, errors] = LexWithDiag("a\n\n\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 4u);
}

TEST(LexerA94, SpaceAdvancesColumn) {
  auto [tokens, errors] = LexWithDiag("a   b");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.column, 5u);
}

TEST(LexerA94, CarriageReturnIsWhitespace) {

  auto tokens = Lex("a\rb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, VerticalTabIsWhitespace) {

  auto tokens = Lex("a\vb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, CrLfPairIsWhitespace) {

  auto tokens = Lex("a\r\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, EscapedIdentTerminatedBySpace) {

  auto tokens = Lex("\\esc_id ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA94, EscapedIdentTerminatedByTab) {
  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA94, EscapedIdentTerminatedByNewline) {
  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA94, EscapedIdentTerminatedByFormfeed) {

  auto tokens = Lex("\\esc_id\f");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA94, EscapedIdentTerminatedByEof) {

  auto tokens = Lex("\\esc_id");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA94, StringLiteralPreservesSpaces) {

  auto tokens = Lex("\"a b c\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"a b c\"");
}

TEST(LexerA94, StringLiteralPreservesTabs) {

  auto tokens = Lex("\"a\tb\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"a\tb\"");
}

TEST(LexerA94, NoErrorsForAllWhitespaceTypes) {

  auto [tokens, errors] = LexWithDiag(
      "module m;\n"
      "\tlogic\fa;\n"
      "endmodule\n");
  EXPECT_FALSE(errors);
}

TEST(LexerA94, NoErrorsForWhitespaceOnlySource) {
  auto [tokens, errors] = LexWithDiag("   \t\n\f  ");
  EXPECT_FALSE(errors);
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}
