#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LevelSensitiveEventLexing, WaitKeyword) {
  auto r = LexOne("wait");
  EXPECT_EQ(r.token.kind, TokenKind::kKwWait);
  EXPECT_EQ(r.token.text, "wait");
}

TEST(LevelSensitiveEventLexing, WaitFollowedByLParen) {
  auto tokens = Lex("wait(");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwWait);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
}

TEST(LevelSensitiveEventLexing, WaitFollowedByWhitespaceAndLParen) {
  auto tokens = Lex("wait (");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwWait);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
}

}  // namespace
