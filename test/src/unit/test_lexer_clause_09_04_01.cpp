#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DelayControlLexing, HashToken) {
  auto r = LexOne("# ");
  EXPECT_EQ(r.token.kind, TokenKind::kHash);
  EXPECT_EQ(r.token.text, "#");
}

TEST(DelayControlLexing, HashFollowedByIntegerLiteral) {
  auto tokens = Lex("#10");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(DelayControlLexing, HashFollowedByZero) {
  auto tokens = Lex("#0");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(DelayControlLexing, HashFollowedByRealLiteral) {
  auto tokens = Lex("#3.5");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[1].kind, TokenKind::kRealLiteral);
}

TEST(DelayControlLexing, HashFollowedByParenthesizedExpression) {
  auto tokens = Lex("#(a + b)");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
}

TEST(DelayControlLexing, HashFollowedByIdentifier) {
  auto tokens = Lex("#tDelay");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(DelayControlLexing, HashNotConfusedWithHashHash) {
  auto tokens = Lex("# 10");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHash);
}

}  // namespace
