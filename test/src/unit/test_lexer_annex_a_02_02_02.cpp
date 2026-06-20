

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(StrengthKeywordLexing, Supply0Keyword) {
  auto tokens = Lex("supply0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSupply0);
}

TEST(StrengthKeywordLexing, Strong0Keyword) {
  auto tokens = Lex("strong0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwStrong0);
}

TEST(StrengthKeywordLexing, Pull0Keyword) {
  auto tokens = Lex("pull0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPull0);
}

TEST(StrengthKeywordLexing, Weak0Keyword) {
  auto tokens = Lex("weak0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwWeak0);
}

TEST(StrengthKeywordLexing, Highz0Keyword) {
  auto tokens = Lex("highz0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwHighz0);
}

TEST(StrengthKeywordLexing, Supply1Keyword) {
  auto tokens = Lex("supply1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSupply1);
}

TEST(StrengthKeywordLexing, Strong1Keyword) {
  auto tokens = Lex("strong1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwStrong1);
}

TEST(StrengthKeywordLexing, Pull1Keyword) {
  auto tokens = Lex("pull1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPull1);
}

TEST(StrengthKeywordLexing, Weak1Keyword) {
  auto tokens = Lex("weak1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwWeak1);
}

TEST(StrengthKeywordLexing, Highz1Keyword) {
  auto tokens = Lex("highz1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwHighz1);
}

TEST(StrengthKeywordLexing, StrengthPairProducesTwoKeywords) {
  auto tokens = Lex("(strong0, weak1)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwStrong0);
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwWeak1);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRParen);
}

TEST(StrengthKeywordLexing, SmallKeyword) {
  auto tokens = Lex("small");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSmall);
}

TEST(StrengthKeywordLexing, MediumKeyword) {
  auto tokens = Lex("medium");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwMedium);
}

TEST(StrengthKeywordLexing, LargeKeyword) {
  auto tokens = Lex("large");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLarge);
}

}  // namespace
