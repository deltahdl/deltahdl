#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DisableForkLexing, DisableForkTokenSequence) {
  auto tokens = Lex("disable fork;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwDisable);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwFork);
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

}  // namespace
