#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(EventDataType, EventKeywordToken) {
  auto tokens = Lex("event");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwEvent);
}
