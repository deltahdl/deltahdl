#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(StringDataType, StringKeywordToken) {
  auto tokens = Lex("string");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwString);
}
