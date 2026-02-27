#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// --- §5.12: Attributes ---

TEST(LexerCh512, AttrDoesNotConfuseMultiply) {
  // §5.12: (* starts an attribute; (a * b) should NOT produce kAttrStart.
  auto tokens = Lex("(a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}
