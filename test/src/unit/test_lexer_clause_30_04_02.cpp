#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(LexerCh30402, StarGtToken) {

  auto tokens = Lex("*>");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStarGt);
}
