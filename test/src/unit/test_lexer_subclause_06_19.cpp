#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(Enumerations, EnumKeywordToken) {
  auto tokens = Lex("enum");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwEnum);
}
