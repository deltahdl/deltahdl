#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §A.9.4: white_space ::= space | tab | newline | formfeed | eof

TEST(WhiteSpaceLexing, SpaceIsWhitespace) {
  auto tokens = Lex("a b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, TabIsWhitespace) {
  auto tokens = Lex("a\tb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, NewlineIsWhitespace) {
  auto tokens = Lex("a\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(WhiteSpaceLexing, FormfeedIsWhitespace) {
  auto tokens = Lex("a\fb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// Bare end-of-file (no preceding explicit whitespace) must terminate the
// preceding token just as the other whitespace characters do — the operational
// meaning of EOF being a member of the white_space category.
TEST(WhiteSpaceLexing, EndOfFileIsWhitespaceTerminator) {
  auto tokens = Lex("abc");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

}  // namespace
