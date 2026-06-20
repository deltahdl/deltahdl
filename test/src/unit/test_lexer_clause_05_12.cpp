#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, DisambiguatesFromMultiply) {
  auto tokens = Lex("(a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}

TEST(LexicalConventionLexing, DisambiguatesCloseFromMultiplyParen) {
  auto tokens = Lex("a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
}

TEST(LexicalConventionLexing, MultipleSeparateInstancesTokens) {
  auto tokens = Lex("(* foo *) (* bar *)");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
  EXPECT_EQ(tokens[3].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].kind, TokenKind::kAttrEnd);
}

TEST(LexicalConventionLexing, AttrFollowedByMultiply) {
  auto tokens = Lex("(* mark *) a * b");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
  EXPECT_EQ(tokens[4].kind, TokenKind::kStar);
}

}  // namespace
