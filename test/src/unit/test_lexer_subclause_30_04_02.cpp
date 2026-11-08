#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

TEST(SpecifyPathTokenLexing, StarGtToken) {
  auto tokens = Lex("*>");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStarGt);
}

TEST(SpecifyPathTokenLexing, EqGtToken) {
  auto tokens = Lex("=>");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEqGt);
}
