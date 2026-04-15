
#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(WildcardPortConnectionLexing, WildcardTokenSequence) {
  auto tokens = Lex("sub u0(.*)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDotStar);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRParen);
}

TEST(WildcardPortConnectionLexing, WildcardMixedWithNamed) {
  auto tokens = Lex("sub u0(.a(x), .*)");
  ASSERT_GE(tokens.size(), 10u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].text, "a");
  EXPECT_EQ(tokens[8].kind, TokenKind::kDotStar);
  EXPECT_EQ(tokens[9].kind, TokenKind::kRParen);
}

TEST(WildcardPortConnectionLexing, WildcardBeforeNamed) {
  auto tokens = Lex("sub u0(.*, .a(x))");
  ASSERT_GE(tokens.size(), 10u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDotStar);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kDot);
}

TEST(WildcardPortConnectionLexing, WildcardWithEmptyPortOverride) {
  auto tokens = Lex("sub u0(.*, .z())");
  ASSERT_GE(tokens.size(), 10u);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDotStar);
  EXPECT_EQ(tokens[7].text, "z");
  EXPECT_EQ(tokens[8].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[9].kind, TokenKind::kRParen);
}

}  // namespace
