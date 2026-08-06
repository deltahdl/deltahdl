

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(PullGateLexing, PullupTokenSequence) {
  auto tokens = Lex("pullup (net1);");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPullup);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(PullGateLexing, PulldownTokenSequence) {
  auto tokens = Lex("pulldown (net1);");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPulldown);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

}  // namespace
