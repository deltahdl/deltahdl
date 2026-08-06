#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NetAliasingLexing, AliasKeyword) {
  auto r = LexOne("alias");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlias);
}

TEST(NetAliasingLexing, AliasThreeNetsTokenSequence) {
  auto tokens = Lex("alias a = b = c ;");
  int eq_count = 0;
  for (auto& t : tokens) {
    if (t.kind == TokenKind::kEq) eq_count++;
  }
  EXPECT_EQ(eq_count, 2);
}

}  // namespace
