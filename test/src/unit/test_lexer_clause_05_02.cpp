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

// Negative form of the free-format separator rule: whitespace between two
// word tokens is significant precisely because removing it fuses them into a
// single token. "foo bar" is two identifiers; "foobar" is one.
TEST(LexicalConventionLexing, AdjacentWordTokensRequireSeparator) {
  auto separated = Lex("foo bar");
  ASSERT_EQ(separated.size(), 3u);  // ident, ident, EOF
  EXPECT_EQ(separated[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(separated[0].text, "foo");
  EXPECT_EQ(separated[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(separated[1].text, "bar");

  auto merged = Lex("foobar");
  ASSERT_EQ(merged.size(), 2u);  // one ident, EOF
  EXPECT_EQ(merged[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(merged[0].text, "foobar");
}

// Sharper negative: dropping the separator changes meaning, not just count --
// a keyword run together with a following letter is no longer the keyword but
// a single ordinary identifier.
TEST(LexicalConventionLexing, MissingSeparatorMergesKeywordIntoIdentifier) {
  auto spaced = Lex("module m");
  ASSERT_EQ(spaced.size(), 3u);
  EXPECT_EQ(spaced[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(spaced[1].kind, TokenKind::kIdentifier);

  auto merged = Lex("modulem");
  ASSERT_EQ(merged.size(), 2u);
  EXPECT_EQ(merged[0].kind, TokenKind::kIdentifier);  // NOT the keyword
  EXPECT_EQ(merged[0].text, "modulem");
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

TEST(LexicalConventionLexing, TokenStreamAlwaysEndsWithEof) {
  auto tokens = Lex("module m; endmodule");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens.back().kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, KeywordAdjacentToOperator) {
  auto tokens = Lex("module+endmodule");
  ASSERT_EQ(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwEndmodule);
}

TEST(LexicalConventionLexing, NumberAdjacentToOperator) {
  auto tokens = Lex("42+7");
  ASSERT_EQ(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, StringLiteralAdjacentToOtherTokens) {
  auto tokens = Lex("a\"hello\"b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, FreeFormatIdentifierSplitByBlockComment) {
  auto no_comment = Lex("abc");
  auto with_comment = Lex("a/**/bc");
  ASSERT_EQ(no_comment.size(), 2u);
  EXPECT_EQ(no_comment[0].text, "abc");
  ASSERT_EQ(with_comment.size(), 3u);
  EXPECT_EQ(with_comment[0].text, "a");
  EXPECT_EQ(with_comment[1].text, "bc");
}

// The free-format rule of 5.2 says whitespace is not syntactically
// significant beyond separating tokens -- except for escaped identifiers
// (see 5.6.1). These two tests exercise that carve-out using 5.6.1's real
// escaped-identifier syntax (leading backslash). Inside an escaped
// identifier, operator characters are NOT split into their own tokens; the
// run continues until whitespace, which is what actually terminates it.
TEST(LexicalConventionLexing, EscapedIdentifierSuspendsFreeFormatSeparation) {
  // Without the escape, '+' separates three tokens.
  auto plain = Lex("cpu+alu");
  ASSERT_EQ(plain.size(), 4u);
  EXPECT_EQ(plain[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(plain[1].kind, TokenKind::kPlus);
  EXPECT_EQ(plain[2].kind, TokenKind::kIdentifier);

  // With the escape, the whole run is one identifier -- the '+' is absorbed.
  auto escaped = Lex("\\cpu+alu ");
  ASSERT_EQ(escaped.size(), 2u);
  EXPECT_EQ(escaped[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(escaped[0].text, "cpu+alu");
  EXPECT_EQ(escaped[1].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, WhitespaceIsSignificantAsEscapedIdentifierEnd) {
  // The space is significant here: it delimits the escaped identifier's
  // extent rather than being an ignorable separator between two idents.
  auto tokens = Lex("\\a+b c");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "a+b");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "c");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, EmptyInputProducesEofOnly) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, WhitespaceOnlyInputProducesEofOnly) {
  auto tokens = Lex("   \t\n\r\n  \f ");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, LineCommentOnlyInputProducesEofOnly) {
  auto tokens = Lex("// nothing but a line comment\n");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, BlockCommentOnlyInputProducesEofOnly) {
  auto tokens = Lex("/* nothing but a block comment */");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, BlockCommentSpanningMultipleLinesAsSeparator) {
  auto tokens = Lex("a /* line one\n   line two\n   line three */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

}  // namespace
