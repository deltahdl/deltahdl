#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// --- §30.4.2: Simple module paths ---

TEST(LexerCh30402, StarGtToken) {
  // §30.4.2: *> establishes a full connection in specify paths.
  auto tokens = Lex("*>");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStarGt);
}
