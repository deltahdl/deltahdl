#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §16.17: the expect statement is introduced by the `expect` keyword, which the
// lexer recognizes as its own keyword token rather than an identifier.
TEST(ExpectStatementLexing, ExpectKeywordRoundTrip) {
  auto tokens = Lex("expect");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwExpect);
}

// §16.17: only the exact `expect` spelling is the keyword. An identifier that
// merely begins with those letters is an ordinary identifier, so a user may
// name a variable `expected` without colliding with the statement keyword.
TEST(ExpectStatementLexing, ExpectKeywordIsNotAPrefixMatch) {
  auto tokens = Lex("expected");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
}

}  // namespace
