#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_12_AttrStartEndTokens) {
  auto tokens = Lex("(* foo *)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(LexerClause05, Cl5_12_AttrWithValueTokens) {
  auto tokens = Lex("(* depth = 8 *)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(LexerClause05, Cl5_12_MultipleAttrSpecs) {
  auto tokens = Lex("(* full_case, parallel_case *)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(LexerClause05, Cl5_12_DisambiguatesFromMultiply) {
  auto tokens = Lex("(a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}

TEST(LexerClause05, Cl5_12_DisambiguatesCloseFromMultiplyParen) {

  auto tokens = Lex("a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
}

TEST(LexerClause05, Cl5_12_AttrWithStringValue) {
  auto tokens = Lex("(* mode = \"cla\" *)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[3].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

}
