#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(InitialProcedureLexing, InitialKeyword) {
  auto r = LexOne("initial ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInitial);
  EXPECT_EQ(r.token.text, "initial");
}

TEST(InitialProcedureLexing, InitialPrefixIsIdentifier) {
  auto r = LexOne("initial_value ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "initial_value");
}

TEST(InitialProcedureLexing, InitialFollowedByStatement) {
  auto tokens = Lex("initial x = 1;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInitial);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
