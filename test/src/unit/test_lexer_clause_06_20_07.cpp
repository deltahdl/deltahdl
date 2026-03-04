#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(LexerCh62007, DollarToken) {
  auto tokens = Lex("$");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}
