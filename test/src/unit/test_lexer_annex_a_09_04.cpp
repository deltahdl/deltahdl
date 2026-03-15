#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

TEST(WhiteSpaceLexing, SpaceSeparatesTokens) {
  auto tokens = Lex("a b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, TabSeparatesTokens) {
  auto tokens = Lex("a\tb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, NewlineSeparatesTokens) {
  auto tokens = Lex("a\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, FormfeedSeparatesTokens) {
  auto tokens = Lex("a\fb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, EofTerminatesTokenStream) {
  auto tokens = Lex("a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, EofOnEmptyInput) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, WhitespaceIgnoredBetweenOperators) {
  auto tokens = Lex("a+b");
  ASSERT_EQ(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].text, "b");
}

TEST(WhiteSpaceLexing, MultipleSpacesIgnored) {
  auto tokens = Lex("a     b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, MixedWhitespaceIgnored) {
  auto tokens = Lex("a \t \n \f b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, LeadingWhitespaceIgnored) {
  auto tokens = Lex("  \t\n  a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(WhiteSpaceLexing, TrailingWhitespaceIgnored) {
  auto tokens = Lex("a  \t\n  ");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, OnlyWhitespaceInput) {
  auto tokens = Lex("   \t\t\n\n\f  ");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, WhitespaceRequiredBetweenKeywords) {
  auto tokens = Lex("moduleendmodule");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "moduleendmodule");
}

TEST(WhiteSpaceLexing, WhitespaceCorrectlySeparatesKeywords) {
  auto tokens = Lex("module endmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(WhiteSpaceLexing, FormfeedSeparatesKeywords) {
  auto tokens = Lex("module\fendmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(WhiteSpaceLexing, TabSeparatesKeywords) {
  auto tokens = Lex("module\tendmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(WhiteSpaceLexing, NewlineSeparatesKeywords) {
  auto tokens = Lex("module\nendmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(WhiteSpaceLexing, NewlineAdvancesLineNumber) {
  auto [tokens, errors] = LexWithDiag("a\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 2u);
}

TEST(WhiteSpaceLexing, TabAdvancesColumn) {
  auto [tokens, errors] = LexWithDiag("a\tb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.column, 3u);
}

TEST(WhiteSpaceLexing, FormfeedAdvancesColumn) {
  auto [tokens, errors] = LexWithDiag("a\fb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.column, 3u);
}

TEST(WhiteSpaceLexing, MultipleNewlinesTrackCorrectly) {
  auto [tokens, errors] = LexWithDiag("a\n\n\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 4u);
}

TEST(WhiteSpaceLexing, SpaceAdvancesColumn) {
  auto [tokens, errors] = LexWithDiag("a   b");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.column, 5u);
}

TEST(WhiteSpaceLexing, CarriageReturnIsWhitespace) {
  auto tokens = Lex("a\rb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, VerticalTabIsWhitespace) {
  auto tokens = Lex("a\vb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, CrLfPairIsWhitespace) {
  auto tokens = Lex("a\r\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, EscapedIdentTerminatedBySpace) {
  auto tokens = Lex("\\esc_id ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "esc_id");
}

TEST(WhiteSpaceLexing, EscapedIdentTerminatedByTab) {
  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "esc_id");
}

TEST(WhiteSpaceLexing, EscapedIdentTerminatedByNewline) {
  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "esc_id");
}

TEST(WhiteSpaceLexing, EscapedIdentTerminatedByFormfeed) {
  auto tokens = Lex("\\esc_id\f");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "esc_id");
}

TEST(WhiteSpaceLexing, EscapedIdentTerminatedByEof) {
  auto tokens = Lex("\\esc_id");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "esc_id");
}

TEST(WhiteSpaceLexing, StringLiteralPreservesSpaces) {
  auto tokens = Lex("\"a b c\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"a b c\"");
}

TEST(WhiteSpaceLexing, StringLiteralPreservesTabs) {
  auto tokens = Lex("\"a\tb\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"a\tb\"");
}

TEST(WhiteSpaceLexing, NoErrorsForAllWhitespaceTypes) {
  auto [tokens, errors] = LexWithDiag(
      "module m;\n"
      "\tlogic\fa;\n"
      "endmodule\n");
  EXPECT_FALSE(errors);
}

TEST(WhiteSpaceLexing, NoErrorsForWhitespaceOnlySource) {
  auto [tokens, errors] = LexWithDiag("   \t\n\f  ");
  EXPECT_FALSE(errors);
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}
