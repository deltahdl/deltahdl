#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_11_PositionalArrayLiteralTokens) {

  auto tokens = Lex("'{0, 1, 2}");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[6].kind, TokenKind::kRBrace);
}

TEST(LexerClause05, Cl5_11_NestedArrayLiteralTokens) {

  auto tokens = Lex("'{'{0,1,2},'{3{4}}}");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(LexerClause05, Cl5_11_ReplicationArrayTokens) {

  auto tokens = Lex("'{3{4}}");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
}

TEST(LexerClause05, Cl5_11_IndexKeyDefaultTokens) {

  auto tokens = Lex("'{1:1, default:0}");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kKwDefault);
  EXPECT_EQ(tokens[6].kind, TokenKind::kColon);
}

TEST(LexerClause05, Cl5_11_TypePrefixedTokens) {

  auto tokens = Lex("triple'{0,1,2}");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(LexerClause05, Cl5_10_ReplicationTokens) {

  auto tokens = Lex("'{3{1}}");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
}

}
