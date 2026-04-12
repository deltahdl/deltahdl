#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NonblockingAssignLexing, OperatorToken) {
  auto r = LexOne("<= ");
  EXPECT_EQ(r.token.kind, TokenKind::kLtEq);
}

TEST(NonblockingAssignLexing, TokenSequence) {
  auto tokens = Lex("q <= d ;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "q");
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "d");
  EXPECT_EQ(tokens[3].kind, TokenKind::kSemicolon);
}

TEST(NonblockingAssignLexing, NoSpacesAroundOperator) {
  auto tokens = Lex("q<=d;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSemicolon);
}

TEST(NonblockingAssignLexing, WithIntraDelayTokenSequence) {
  auto tokens = Lex("q <= #5 d ;");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].kind, TokenKind::kSemicolon);
}

}  // namespace
