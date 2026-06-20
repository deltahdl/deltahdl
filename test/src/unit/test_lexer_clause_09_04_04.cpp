#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LevelSensitiveSequenceLexing, TriggeredLexesAsIdentifier) {
  auto r = LexOne("triggered");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "triggered");
}

TEST(LevelSensitiveSequenceLexing, DotTriggeredAccess) {
  auto tokens = Lex("abc.triggered");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "triggered");
}

TEST(LevelSensitiveSequenceLexing, WaitWithDotTriggered) {
  auto tokens = Lex("wait(abc.triggered)");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwWait);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "triggered");
  EXPECT_EQ(tokens[5].kind, TokenKind::kRParen);
}

}  // namespace
