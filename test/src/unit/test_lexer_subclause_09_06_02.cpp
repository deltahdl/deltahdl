#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DisableStatementLexing, DisableKeyword) {
  auto r = LexOne("disable");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDisable);
  EXPECT_EQ(r.token.text, "disable");
}

TEST(DisableStatementLexing, DisablePrefixIsIdentifier) {
  auto r = LexOne("disable_block ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "disable_block");
}

TEST(DisableStatementLexing, DisableFollowedByIdentifier) {
  auto tokens = Lex("disable my_block;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwDisable);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "my_block");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

TEST(DisableStatementLexing, DisableFollowedByHierarchicalPath) {
  auto tokens = Lex("disable m.always1;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwDisable);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

}  // namespace
