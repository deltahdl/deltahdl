#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, SpaceIsWhitespace) {
  auto tokens = Lex("a b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, TabIsWhitespace) {
  auto tokens = Lex("a\tb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, NewlineIsWhitespace) {
  auto tokens = Lex("a\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, FormfeedIsWhitespace) {
  auto tokens = Lex("a\fb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, VerticalTabIsWhitespace) {
  auto tokens = Lex("a\vb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, CarriageReturnIsWhitespace) {
  auto tokens = Lex("a\rb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, CrlfIsWhitespace) {
  auto tokens = Lex("a\r\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, WhitespaceNotEmittedAsToken) {
  auto tokens = Lex("  \t\n\f\v  a  \t\n\f\v  ");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, WhitespaceOnlySeparatesTokens) {
  auto no_ws = Lex("modulem");
  ASSERT_EQ(no_ws.size(), 2u);
  EXPECT_EQ(no_ws[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(no_ws[0].text, "modulem");

  auto with_ws = Lex("module m");
  ASSERT_EQ(with_ws.size(), 3u);
  EXPECT_EQ(with_ws[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(with_ws[1].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, MixedWhitespaceCollapsesToSeparator) {
  auto tokens = Lex("a  \t  \n  \f  \v  b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, WhitespaceVariationsProduceSameTokenKinds) {
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

TEST(LexicalConventionLexing, SpacesPreservedInStringLiteral) {
  auto r = LexOne("\"  hello   world  \"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_NE(r.token.text.find("  hello   world  "), std::string_view::npos);
}

TEST(LexicalConventionLexing, TabsPreservedInStringLiteral) {
  auto r = LexOne("\"\thello\tworld\t\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_NE(r.token.text.find("\thello\tworld\t"), std::string_view::npos);
}

TEST(LexicalConventionLexing, MixedSpacesAndTabsInStringLiteral) {
  auto r = LexOne("\" \t mixed \t \"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_NE(r.token.text.find(" \t mixed \t "), std::string_view::npos);
}

TEST(LexicalConventionLexing, StringLiteralWithOnlySpaces) {
  auto r = LexOne("\"   \"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, StringLiteralWithOnlyTabs) {
  auto r = LexOne("\"\t\t\t\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, SourceLocationsAcrossNewlines) {
  auto tokens = Lex("a\nb c");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.line, 2u);
  EXPECT_EQ(tokens[1].loc.column, 1u);
  EXPECT_EQ(tokens[2].loc.line, 2u);
  EXPECT_EQ(tokens[2].loc.column, 3u);
}

TEST(LexicalConventionLexing, SourceLocationsAcrossTabsAndSpaces) {
  auto tokens = Lex("a\t\tb");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 1u);

  EXPECT_GT(tokens[1].loc.column, 1u);
}

TEST(LexicalConventionLexing, WhitespaceOnlyInputProducesEof) {
  auto tokens = Lex("   \t\n\f\v\r\n   ");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, LeadingWhitespaceBeforeToken) {
  auto tokens = Lex("   a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(LexicalConventionLexing, TrailingWhitespaceAfterToken) {
  auto tokens = Lex("a   ");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(LexicalConventionLexing, FormfeedSeparatesKeywords) {
  auto tokens = Lex("module\fm");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, VerticalTabSeparatesKeywords) {
  auto tokens = Lex("module\vm");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
