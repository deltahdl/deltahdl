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

// Degenerate form of the eof alternative: with no preceding characters, the
// lexer's first call must still recognise EOF as white_space and produce the
// EOF token rather than e.g. looping or erroring.
TEST(WhiteSpaceLexing, EmptyInputProducesOnlyEofToken) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

// All four non-EOF alternatives appearing together must each be consumed by
// the white_space rule, leaving only the EOF terminator in the stream.
TEST(WhiteSpaceLexing, WhitespaceOnlyInputProducesOnlyEofToken) {
  auto tokens = Lex(" \t\n\f");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

// The white_space rule applies independently per character: a run of the same
// alternative between two tokens must all be consumed, not just the first.
TEST(WhiteSpaceLexing, MultipleConsecutiveSpacesAreEachWhitespace) {
  auto tokens = Lex("a   b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

// The white_space rule's alternatives are interchangeable: a mix of all four
// non-EOF members appearing between two tokens must each match the rule.
TEST(WhiteSpaceLexing, MixedWhitespaceCharactersBetweenTokens) {
  auto tokens = Lex("a \t\n\fb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

}  // namespace
