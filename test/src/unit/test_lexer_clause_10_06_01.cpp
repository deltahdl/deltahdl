#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ProceduralAssignDeassignLexing, AssignKeyword) {
  auto r = LexOne("assign");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAssign);
}

TEST(ProceduralAssignDeassignLexing, DeassignKeyword) {
  auto r = LexOne("deassign");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDeassign);
}

TEST(ProceduralAssignDeassignLexing, AssignStatementTokenSequence) {
  auto tokens = Lex("assign q = 1 ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAssign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(ProceduralAssignDeassignLexing, DeassignStatementTokenSequence) {
  auto tokens = Lex("deassign q ;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwDeassign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

TEST(ProceduralAssignDeassignLexing, AssignExpressionRhsTokenSequence) {
  auto tokens = Lex("assign c = a + b ;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAssign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].kind, TokenKind::kSemicolon);
}

TEST(ProceduralAssignDeassignLexing, AssignConcatLhsTokenSequence) {
  auto tokens = Lex("assign { a , b } = 1 ;");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAssign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[6].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[7].kind, TokenKind::kIntLiteral);
}

}  // namespace
