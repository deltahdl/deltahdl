#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

TEST(UserDefinedTypes, TypedefKeywordToken) {
  auto tokens = Lex("typedef");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTypedef);
}
