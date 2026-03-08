#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_3_SpaceIsWhitespace) {
  auto tokens = Lex("a b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_3_TabIsWhitespace) {
  auto tokens = Lex("a\tb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_3_NewlineIsWhitespace) {
  auto tokens = Lex("a\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_3_FormfeedIsWhitespace) {
  auto tokens = Lex("a\fb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_3_VerticalTabIsWhitespace) {
  auto tokens = Lex("a\vb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_3_CarriageReturnIsWhitespace) {
  auto tokens = Lex("a\rb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_3_CrlfIsWhitespace) {
  auto tokens = Lex("a\r\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_3_EofTerminatesTokenStream) {
  auto tokens = Lex("a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexerClause05, Cl5_3_EofOnlyInput) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerClause05, Cl5_3_WhitespaceNotEmittedAsToken) {
  auto tokens = Lex("  \t\n\f\v  a  \t\n\f\v  ");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexerClause05, Cl5_3_WhitespaceOnlySeparatesTokens) {

  auto no_ws = Lex("modulem");
  ASSERT_EQ(no_ws.size(), 2u);
  EXPECT_EQ(no_ws[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(no_ws[0].text, "modulem");

  auto with_ws = Lex("module m");
  ASSERT_EQ(with_ws.size(), 3u);
  EXPECT_EQ(with_ws[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(with_ws[1].kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_3_MixedWhitespaceCollapsesToSeparator) {
  auto tokens = Lex("a  \t  \n  \f  \v  b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_3_WhitespaceVariationsProduceSameTokenKinds) {
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

TEST(LexerClause05, Cl5_3_SpacesPreservedInStringLiteral) {
  auto r = LexOne("\"  hello   world  \"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_NE(r.token.text.find("  hello   world  "), std::string_view::npos);
}

TEST(LexerClause05, Cl5_3_TabsPreservedInStringLiteral) {
  auto r = LexOne("\"\thello\tworld\t\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_NE(r.token.text.find("\thello\tworld\t"), std::string_view::npos);
}

TEST(LexerClause05, Cl5_3_MixedSpacesAndTabsInStringLiteral) {
  auto r = LexOne("\" \t mixed \t \"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_NE(r.token.text.find(" \t mixed \t "), std::string_view::npos);
}

TEST(LexerClause05, Cl5_3_StringLiteralWithOnlySpaces) {
  auto r = LexOne("\"   \"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_3_StringLiteralWithOnlyTabs) {
  auto r = LexOne("\"\t\t\t\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_3_SourceLocationsAcrossNewlines) {
  auto tokens = Lex("a\nb c");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.line, 2u);
  EXPECT_EQ(tokens[1].loc.column, 1u);
  EXPECT_EQ(tokens[2].loc.line, 2u);
  EXPECT_EQ(tokens[2].loc.column, 3u);
}

TEST(LexerClause05, Cl5_3_SourceLocationsAcrossTabsAndSpaces) {
  auto tokens = Lex("a\t\tb");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 1u);

  EXPECT_GT(tokens[1].loc.column, 1u);
}

TEST(LexerClause05, Cl5_3_WhitespaceOnlyInputProducesEof) {
  auto tokens = Lex("   \t\n\f\v\r\n   ");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerClause05, Cl5_3_LeadingWhitespaceBeforeToken) {
  auto tokens = Lex("   a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(LexerClause05, Cl5_3_TrailingWhitespaceAfterToken) {
  auto tokens = Lex("a   ");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(LexerClause05, Cl5_3_OperatorsDoNotNeedWhitespaceSeparation) {
  auto tokens = Lex("a+b");
  ASSERT_EQ(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].text, "b");
}

}
