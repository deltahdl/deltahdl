
#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NamedPortLexer, NamedPortTokenSequence) {
  auto tokens = Lex("sub u0(.a(x))");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "sub");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "u0");
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "a");
  EXPECT_EQ(tokens[5].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[6].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].text, "x");
  EXPECT_EQ(tokens[7].kind, TokenKind::kRParen);
}

TEST(NamedPortLexer, EmptyNamedPortTokenSequence) {
  auto tokens = Lex("sub u0(.a())");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "a");
  EXPECT_EQ(tokens[5].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[6].kind, TokenKind::kRParen);
}

TEST(NamedPortLexer, MultipleNamedPortsTokenSequence) {
  auto tokens = Lex("sub u0(.a(x), .b(y))");
  ASSERT_GE(tokens.size(), 14u);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].text, "a");
  EXPECT_EQ(tokens[8].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[9].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[10].text, "b");
}

}  // namespace
