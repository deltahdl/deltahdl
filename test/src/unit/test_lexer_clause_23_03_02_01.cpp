
#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(OrderedPortLexer, OrderedPortTokenSequence) {
  auto tokens = Lex("sub u0(a, b)");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "sub");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "u0");
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "a");
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].text, "b");
  EXPECT_EQ(tokens[6].kind, TokenKind::kRParen);
}

TEST(OrderedPortLexer, BlankOrderedPortTokenSequence) {
  auto tokens = Lex("sub u0(a, , c)");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "a");
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[6].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].text, "c");
  EXPECT_EQ(tokens[7].kind, TokenKind::kRParen);
}

TEST(OrderedPortLexer, AllBlankPortsTokenSequence) {
  auto tokens = Lex("sub u0(, , )");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRParen);
}

}  // namespace
