#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §10.4.1 BNF: blocking_assignment ::= variable_lvalue = ... .  The simple
// `=` assignment operator is the head token that distinguishes a blocking
// procedural assignment from a nonblocking one.
TEST(BlockingAssignLexing, EqualsOperatorToken) {
  auto r = LexOne("= ");
  EXPECT_EQ(r.token.kind, TokenKind::kEq);
}

TEST(BlockingAssignLexing, TokenSequence) {
  auto tokens = Lex("a = b ;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "b");
  EXPECT_EQ(tokens[3].kind, TokenKind::kSemicolon);
}

TEST(BlockingAssignLexing, NoSpacesAroundOperator) {
  auto tokens = Lex("a=b;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSemicolon);
}

// §10.4.1: intra-assignment timing control is a `=` followed by `#delay`.
// The lexer must split this into kEq, kHash, kIntLiteral so the parser can
// pick up the optional delay_or_event_control.
TEST(BlockingAssignLexing, WithIntraDelayTokenSequence) {
  auto tokens = Lex("a = #5 b ;");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].kind, TokenKind::kSemicolon);
}

TEST(BlockingAssignLexing, EqualsDistinctFromLtEq) {
  auto tokens = Lex("= <=");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtEq);
}

}  // namespace
