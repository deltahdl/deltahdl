
#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ImplicitNamedPortConnectionLexing, ImplicitPortTokenSequence) {
  auto tokens = Lex("sub u0(.a, .b)");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "a");
  EXPECT_EQ(tokens[5].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[6].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[7].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[7].text, "b");
  EXPECT_EQ(tokens[8].kind, TokenKind::kRParen);
}

TEST(ImplicitNamedPortConnectionLexing, NoParenthesesAfterImplicitPortName) {
  auto tokens = Lex("sub u0(.a, .b(x))");
  ASSERT_GE(tokens.size(), 12u);
  EXPECT_EQ(tokens[4].text, "a");
  EXPECT_EQ(tokens[5].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[7].text, "b");
  EXPECT_EQ(tokens[8].kind, TokenKind::kLParen);
}

}  // namespace
