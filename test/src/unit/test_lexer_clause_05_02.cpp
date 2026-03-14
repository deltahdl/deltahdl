#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, EachTokenHasOneOrMoreChars) {
  auto tokens = Lex("module m; logic [7:0] x = 8'hFF + 1; endmodule");
  for (size_t i = 0; i + 1 < tokens.size(); ++i) {
    EXPECT_GE(tokens[i].text.size(), 1u)
        << "token " << i << " (" << tokens[i].text << ") is empty";
  }
}

TEST(LexicalConventionLexing, SingleCharTokensHaveSizeOne) {
  auto tokens = Lex("+ ; , ( )");
  for (size_t i = 0; i + 1 < tokens.size(); ++i) {
    EXPECT_EQ(tokens[i].text.size(), 1u);
  }
}

TEST(LexicalConventionLexing, MultiCharTokensHaveSizeGreaterThanOne) {
  auto r = LexOne("module");
  EXPECT_GT(r.token.text.size(), 1u);

  auto r2 = LexOne("8'hFF");
  EXPECT_GT(r2.token.text.size(), 1u);
}

TEST(LexicalConventionLexing, FreeFormatTokensOnOneLine) {
  auto tokens = Lex("module m;logic a;endmodule");
  bool has_module = false;
  bool has_endmodule = false;
  for (const auto& tok : tokens) {
    if (tok.kind == TokenKind::kKwModule) has_module = true;
    if (tok.kind == TokenKind::kKwEndmodule) has_endmodule = true;
  }
  EXPECT_TRUE(has_module);
  EXPECT_TRUE(has_endmodule);
}

TEST(LexicalConventionLexing, FreeFormatTokensSplitAcrossLines) {
  auto tokens = Lex("module\nm\n;\nendmodule\n");
  bool has_module = false;
  bool has_semi = false;
  bool has_ident = false;
  for (const auto& tok : tokens) {
    if (tok.kind == TokenKind::kKwModule) has_module = true;
    if (tok.kind == TokenKind::kSemicolon) has_semi = true;
    if (tok.kind == TokenKind::kIdentifier) has_ident = true;
  }
  EXPECT_TRUE(has_module);
  EXPECT_TRUE(has_semi);
  EXPECT_TRUE(has_ident);
}

TEST(LexicalConventionLexing, WhitespaceVariationsProduceSameTokens) {
  auto compact = Lex("a+b");
  auto spaced = Lex("a + b");
  auto tabbed = Lex("a\t+\tb");
  auto newlined = Lex("a\n+\nb");

  ASSERT_EQ(compact.size(), 4u);
  ASSERT_EQ(spaced.size(), 4u);
  ASSERT_EQ(tabbed.size(), 4u);
  ASSERT_EQ(newlined.size(), 4u);

  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(compact[i].kind, spaced[i].kind);
    EXPECT_EQ(compact[i].kind, tabbed[i].kind);
    EXPECT_EQ(compact[i].kind, newlined[i].kind);
  }
}

TEST(LexicalConventionLexing, MultipleSpacesBetweenTokensCollapse) {
  auto tokens = Lex("a      b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, MixedWhitespaceAsTokenSeparators) {
  auto tokens = Lex("a \t \n \r\n b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, EscapedIdentifierTerminatedBySpace) {
  auto tokens = Lex("\\abc def");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
}

TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByNewline) {
  auto tokens = Lex("\\abc\ndef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
}

TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByTab) {
  auto tokens = Lex("\\abc\tdef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, EscapedIdentifierIncludesSpecialChars) {
  auto r = LexOne("\\a+b*c ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
}

TEST(LexicalConventionLexing, WhitespaceCategory) {
  auto tokens = Lex("   ");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, CommentCategory) {
  auto tokens = Lex("a // line comment\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, OperatorCategory) {
  auto r = LexOne("<=");
  EXPECT_EQ(r.token.kind, TokenKind::kLtEq);
}

TEST(LexicalConventionLexing, NumberCategory) {
  auto r = LexOne("42");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, StringLiteralCategory) {
  auto r = LexOne("\"test\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, IdentifierCategory) {
  auto r = LexOne("my_var");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, KeywordCategory) {
  auto r = LexOne("always");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlways);
}

TEST(LexicalConventionLexing, AllSevenCategoriesInOneStream) {
  auto tokens = Lex("module /* comment */ m; logic x = 42 + \"s\"; endmodule");
  bool has_operator = false;
  bool has_number = false;
  bool has_string = false;
  bool has_identifier = false;
  bool has_keyword = false;

  for (const auto& tok : tokens) {
    if (tok.kind == TokenKind::kPlus) has_operator = true;
    if (tok.kind == TokenKind::kIntLiteral) has_number = true;
    if (tok.kind == TokenKind::kStringLiteral) has_string = true;
    if (tok.kind == TokenKind::kIdentifier) has_identifier = true;
    if (tok.kind == TokenKind::kKwModule) has_keyword = true;
  }

  EXPECT_TRUE(has_operator);
  EXPECT_TRUE(has_number);
  EXPECT_TRUE(has_string);
  EXPECT_TRUE(has_identifier);
  EXPECT_TRUE(has_keyword);
}

TEST(LexicalConventionLexing, AdjacentOperatorsWithoutWhitespace) {
  auto tokens = Lex("a+b-c");
  ASSERT_EQ(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, TokensAdjacentToPunctuation) {
  auto tokens = Lex("a(b)");
  ASSERT_EQ(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
}

TEST(LexicalConventionLexing, FormfeedIsWhitespace) {
  auto tokens = Lex("a\fb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

}  // namespace
