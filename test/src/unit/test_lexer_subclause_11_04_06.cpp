#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

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
