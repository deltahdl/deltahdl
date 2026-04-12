#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ConditionalEventIffLexing, IffKeywordInEventControl) {
  auto tokens = Lex("@(posedge clk iff en)");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwPosedge);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwIff);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].kind, TokenKind::kRParen);
}

TEST(ConditionalEventIffLexing, IffWithEqualityCondition) {
  auto tokens = Lex("@(a iff enable == 1)");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwIff);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].kind, TokenKind::kEqEq);
  EXPECT_EQ(tokens[6].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[7].kind, TokenKind::kRParen);
}

TEST(ConditionalEventIffLexing, IffIsKeywordNotIdentifier) {
  auto tokens = Lex("iff");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwIff);
}

TEST(ConditionalEventIffLexing, IffWithOrSeparator) {
  auto tokens = Lex("@(posedge clk iff en or negedge rst)");
  ASSERT_GE(tokens.size(), 10u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwIff);
  EXPECT_EQ(tokens[6].kind, TokenKind::kKwOr);
  EXPECT_EQ(tokens[7].kind, TokenKind::kKwNegedge);
}

TEST(ConditionalEventIffLexing, IffWithNegedge) {
  auto tokens = Lex("@(negedge clk iff !rst)");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwNegedge);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwIff);
}

TEST(ConditionalEventIffLexing, IffWithEdgeKeyword) {
  auto tokens = Lex("@(edge sig iff guard)");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwEdge);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwIff);
}

}  // namespace
