#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

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

TEST(WhiteSpaceLexing, EndOfFileIsWhitespaceTerminator) {
  auto tokens = Lex("abc");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, EmptyInputProducesOnlyEofToken) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

// A run mixing every printing white_space alternative (space, tab, newline,
// formfeed) collapses to a single token boundary: the rule discards white space
// rather than emitting a token per character, so two tokens remain, not more.
TEST(WhiteSpaceLexing, MixedRunOfWhitespaceCollapsesToSingleSeparator) {
  auto tokens = Lex("a \t\n\f b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

// Leading and trailing white space is discarded, not turned into empty or
// whitespace tokens: a single identifier surrounded by white space yields only
// that identifier followed by eof.
TEST(WhiteSpaceLexing, LeadingAndTrailingWhitespaceIsDiscarded) {
  auto tokens = Lex(" \t a \n ");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

}  // namespace
