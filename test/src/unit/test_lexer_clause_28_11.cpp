// §28.11

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// Each strength0 keyword must lex to its own token kind so the parser can tell
// them apart without reparsing the identifier text.
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

// Strength1 keywords follow the same pattern but must be distinct from their
// strength0 counterparts.
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

// A strength0 and strength1 keyword paired in parentheses must lex to two
// distinct keyword tokens — the pair is not a single compound token.
TEST(StrengthKeywordLexing, StrengthPairProducesTwoKeywords) {
  auto tokens = Lex("(strong0, weak1)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwStrong0);
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwWeak1);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRParen);
}

// The three charge storage strengths are unsuffixed keywords (no 0/1); each
// must lex to a dedicated token kind, distinct from the drive-strength set.
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
