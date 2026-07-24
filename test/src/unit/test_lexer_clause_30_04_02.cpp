#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(SpecifyPathTokenLexing, StarGtToken) {
  auto tokens = Lex("*>");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStarGt);
}

// §30.4.2 declares simple paths in two forms: "source *> destination" and
// "source => destination". The full-connection operator is lexed above; this
// observes the parallel-connection operator '=>' as its own token, the other
// half of Syntax 30-3's operator pair.
TEST(SpecifyPathTokenLexing, EqGtToken) {
  auto tokens = Lex("=>");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEqGt);
}
