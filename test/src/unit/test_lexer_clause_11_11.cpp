#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(MinTypMaxLexing, ColonSeparatedTriplet) {
  auto tokens = Lex("1:2:3");
  ASSERT_GE(tokens.size(), 6);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntegerLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntegerLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIntegerLiteral);
}

TEST(MinTypMaxLexing, ColonNotDoubleColon) {
  auto tokens = Lex("10 : 20 : 30");
  ASSERT_GE(tokens.size(), 6);
  EXPECT_EQ(tokens[1].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kColon);
}
