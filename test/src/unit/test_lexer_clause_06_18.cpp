#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// §6.18 User-defined types (typedef)

TEST(UserDefinedTypes, TypedefKeywordToken) {
  auto tokens = Lex("typedef");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTypedef);
}
