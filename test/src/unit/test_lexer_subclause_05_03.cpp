#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

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

// §5.3 and A.9.4 make white space the space, tab, newline, formfeed and end
// of file alone, so a vertical tab separates nothing. No token begins with
// one, and §5.2 has it reported as a character outside every token.
TEST(LexicalConventionLexing, VerticalTabIsNoWhitespace) {
  auto diags = LexDiagnostics("a\vb");
  EXPECT_TRUE(ReportedError(diags, "unexpected character '\v'", 1, "5.2"));
}

// An escaped identifier runs to white space (§5.6.1), so a vertical tab, being
// none, stands inside it as the non-printable character it is.
TEST(LexicalConventionLexing, VerticalTabDoesNotEndAnEscapedIdentifier) {
  auto diags = LexDiagnostics("\\ab\vc ");
  EXPECT_TRUE(ReportedError(
      diags, "escaped identifier contains non-printable character", 1,
      "5.6.1"));
}

// §5.7.1 lets white space stand between a based literal's base and its value,
// and a vertical tab is none, so the value is missing where it stands.
TEST(LexicalConventionLexing, VerticalTabDoesNotSeparateABaseFromItsValue) {
  auto diags = LexDiagnostics("4'h\v5 ");
  EXPECT_TRUE(ReportedError(diags, "missing value digits after base specifier",
                            1, "5.7.1"));
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
  auto tokens = Lex("  \t\n\f  a  \t\n\f  ");
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
  auto tokens = Lex("a  \t  \n  \f  b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
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
  auto tokens = Lex("   \t\n\f\r\n   ");
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

TEST(LexicalConventionLexing, EndOfFileTerminatesEachTokenCategory) {
  auto kw = Lex("module");
  ASSERT_EQ(kw.size(), 2u);
  EXPECT_EQ(kw[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(kw[1].kind, TokenKind::kEof);

  auto num = Lex("42");
  ASSERT_EQ(num.size(), 2u);
  EXPECT_EQ(num[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(num[1].kind, TokenKind::kEof);

  auto op = Lex("+");
  ASSERT_EQ(op.size(), 2u);
  EXPECT_EQ(op[0].kind, TokenKind::kPlus);
  EXPECT_EQ(op[1].kind, TokenKind::kEof);

  auto str = Lex("\"hi\"");
  ASSERT_EQ(str.size(), 2u);
  EXPECT_EQ(str[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(str[1].kind, TokenKind::kEof);
}

}  // namespace
