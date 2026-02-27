#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// --- §5.6.1: Escaped identifiers ---

TEST(LexerCh50601, TerminatedByNewline) {
  // §5.6.1: Escaped identifiers end with white space; newline is white space.
  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerCh50601, TerminatedByTab) {
  // §5.6.1: Escaped identifiers end with white space; tab is white space.
  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}
