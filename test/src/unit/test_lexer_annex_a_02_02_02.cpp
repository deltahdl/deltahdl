// §A.2.2.2: lexer-stage coverage of the strength keyword set named in the
// drive_strength, strength0, strength1, and charge_strength productions.

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §A.2.2.2 strength0 keywords: each must lex to its own token kind so the
// parser can branch on direction without rescanning identifier text.
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

// §A.2.2.2 drive_strength alternatives 4-6 reference highz0 directly as a
// terminal; it must lex to its own keyword kind.
TEST(StrengthKeywordLexing, Highz0Keyword) {
  auto tokens = Lex("highz0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwHighz0);
}

// §A.2.2.2 strength1 keywords: distinct from the strength0 set and from one
// another.
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

// §A.2.2.2 drive_strength is two strength tokens separated by a comma inside
// parentheses; lexing must produce five distinct tokens, never one compound.
TEST(StrengthKeywordLexing, StrengthPairProducesTwoKeywords) {
  auto tokens = Lex("(strong0, weak1)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwStrong0);
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwWeak1);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRParen);
}

// §A.2.2.2 charge_strength keywords are unsuffixed (no 0/1) and must lex to
// their own token kinds, distinct from the drive-strength set.
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
