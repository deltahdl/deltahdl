#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ImplicitEventLexing, AtStarTwoTokens) {
  auto tokens = Lex("@*");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStar);
}

TEST(ImplicitEventLexing, AtParenStarParenFourTokens) {
  auto tokens = Lex("@(*)");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
}

TEST(ImplicitEventLexing, AtStarWithSpaceBetween) {
  auto tokens = Lex("@ *");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStar);
}

TEST(ImplicitEventLexing, AtStarFollowedByIdentifier) {
  auto tokens = Lex("@* y");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(ImplicitEventLexing, AtParenStarParenFollowedByIdentifier) {
  auto tokens = Lex("@(*) y");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
}

TEST(ImplicitEventLexing, AtParenSpaceStarParenTokens) {
  auto tokens = Lex("@( *)");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
}

TEST(ImplicitEventLexing, AtParenStarSpaceParenTokens) {
  auto tokens = Lex("@(* )");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
}

}  // namespace
