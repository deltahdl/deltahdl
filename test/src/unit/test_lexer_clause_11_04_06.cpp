#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §11.4.6 defines the wildcard equality (==?) and wildcard inequality (!=?)
// operators. The lexer must recognize each three-character lexeme as one token.

TEST(WildcardEqualityLexing, WildcardEqOperatorToken) {
  auto r = LexOne("==?");
  EXPECT_EQ(r.token.kind, TokenKind::kEqEqQuestion);
  EXPECT_EQ(r.token.text.size(), 3u);
}

TEST(WildcardEqualityLexing, WildcardNeqOperatorToken) {
  auto r = LexOne("!=?");
  EXPECT_EQ(r.token.kind, TokenKind::kBangEqQuestion);
  EXPECT_EQ(r.token.text.size(), 3u);
}

// The operator is taken as a whole rather than split into == / != followed by a
// separate ? token when it sits between two operands.
TEST(WildcardEqualityLexing, WildcardEqIsSingleTokenBetweenOperands) {
  auto tokens = Lex("a ==? b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEqQuestion);
}

TEST(WildcardEqualityLexing, WildcardNeqIsSingleTokenBetweenOperands) {
  auto tokens = Lex("a !=? b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kBangEqQuestion);
}

}  // namespace
