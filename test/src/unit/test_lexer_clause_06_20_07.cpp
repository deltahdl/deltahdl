#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// --- §6.20.7: $ as a constant ---

TEST(LexerCh62007, DollarToken) {
  // §6.20.7: Bare $ is a special constant, not a system identifier.
  auto tokens = Lex("$");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}
