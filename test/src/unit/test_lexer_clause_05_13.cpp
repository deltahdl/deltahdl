#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_13_DotNotationTokens) {

  auto tokens = Lex("arr.size()");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRParen);
}

TEST(LexerClause05, Cl5_13_DotNotationNoParens) {

  auto tokens = Lex("arr.size");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_13_ChainedDotNotation) {

  auto tokens = Lex("obj.arr.size()");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_13_MethodWithArgTokens) {

  auto tokens = Lex("q.push_back(8'hAA)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLParen);
}

}
