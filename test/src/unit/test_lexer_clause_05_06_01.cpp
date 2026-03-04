#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(LexerCh50601, TerminatedByNewline) {

  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerCh50601, TerminatedByTab) {

  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}
