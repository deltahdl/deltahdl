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

TEST(WhiteSpaceLexing, WhitespaceVariationsProduceSameTokenKinds) {
  auto sp = Lex("a b");
  auto tab = Lex("a\tb");
  auto nl = Lex("a\nb");
  auto ff = Lex("a\fb");

  ASSERT_EQ(sp.size(), tab.size());
  ASSERT_EQ(sp.size(), nl.size());
  ASSERT_EQ(sp.size(), ff.size());
  for (size_t i = 0; i < sp.size(); ++i) {
    EXPECT_EQ(sp[i].kind, tab[i].kind) << "index " << i;
    EXPECT_EQ(sp[i].kind, nl[i].kind) << "index " << i;
    EXPECT_EQ(sp[i].kind, ff[i].kind) << "index " << i;
  }
}

TEST(WhiteSpaceLexing, FormfeedSeparatesKeywords) {
  auto tokens = Lex("module\fm");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
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

TEST(WhiteSpaceLexing, EmptyInputProducesOnlyEof) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, WhitespaceOnlyInputProducesOnlyEof) {
  auto tokens = Lex(" \t\n\f");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, LeadingSpaceIsWhitespace) {
  auto tokens = Lex(" a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(WhiteSpaceLexing, LeadingTabIsWhitespace) {
  auto tokens = Lex("\ta");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(WhiteSpaceLexing, LeadingNewlineIsWhitespace) {
  auto tokens = Lex("\na");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(WhiteSpaceLexing, LeadingFormfeedIsWhitespace) {
  auto tokens = Lex("\fa");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(WhiteSpaceLexing, TrailingSpaceBeforeEndOfFile) {
  auto tokens = Lex("a ");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, TrailingTabBeforeEndOfFile) {
  auto tokens = Lex("a\t");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, TrailingNewlineBeforeEndOfFile) {
  auto tokens = Lex("a\n");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(WhiteSpaceLexing, TrailingFormfeedBeforeEndOfFile) {
  auto tokens = Lex("a\f");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

}  // namespace
