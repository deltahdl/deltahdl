#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// §6.19 Enumerations

TEST(Enumerations, EnumKeywordToken) {
  auto tokens = Lex("enum");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwEnum);
}
