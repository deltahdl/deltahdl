#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ContinuousAssignLexing, AssignKeyword) {
  auto r = LexOne("assign");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAssign);
}

TEST(ContinuousAssignLexing, BasicAssignTokenSequence) {
  auto tokens = Lex("assign a = b ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAssign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(ContinuousAssignLexing, AssignWithDelayTokens) {
  auto tokens = Lex("assign #5 a = b ;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAssign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kEq);
}

TEST(ContinuousAssignLexing, AssignWithDriveStrengthTokens) {
  auto tokens = Lex("assign ( strong0 , weak1 ) a = b ;");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAssign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwStrong0);
  EXPECT_EQ(tokens[3].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwWeak1);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRParen);
}

TEST(ContinuousAssignLexing, CommaSeparatedAssignments) {
  auto tokens = Lex("assign a = b , c = d ;");
  int comma_count = 0;
  for (auto& t : tokens) {
    if (t.kind == TokenKind::kComma) comma_count++;
  }
  EXPECT_GE(comma_count, 1);
}

}  // namespace
