#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, EmptyString) {
  auto tokens = Lex("\"\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"");
}

TEST(LexicalConventionLexing, BasicString) {
  auto r = LexOne("\"hello world\" ");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "\"hello world\"");
}

TEST(LexicalConventionLexing, SingleChar) {
  auto r = LexOne("\"A\" ");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "\"A\"");
}

TEST(LexicalConventionLexing, UnterminatedStringError) {
  auto diags = LexDiagnostics("\"unterminated");
  EXPECT_TRUE(ReportedError(diags, "unterminated string literal", 1, "5.9"));
}

TEST(LexicalConventionLexing, UnterminatedNewlineError) {
  auto diags = LexDiagnostics("\"line1\nline2\"");
  EXPECT_TRUE(ReportedError(diags, "unterminated string literal", 1, "5.9"));
}

// A quoted string is contained in a single line unless the newline character is
// immediately preceded by a backslash, so this source is one string literal
// token rather than two lines. What the interpreted value of that continuation
// sequence is belongs to 5.9.1 and is covered in the sibling file.
TEST(LexicalConventionLexing, QuotedStringLineContinuation) {
  std::string src = "\"AB\\\nCD\"";
  auto tokens = Lex(src);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, TripleQuotedBasic) {
  auto tokens = Lex(R"("""hello""")");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, TripleQuotedWithNewline) {
  std::string src = "\"\"\"line1\nline2\"\"\"";
  auto tokens = Lex(src);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, TripleQuotedWithDoubleQuote) {
  auto tokens = Lex(R"("""say "hello" """)");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, TripleQuotedWithEscape) {
  auto tokens = Lex(R"("""hello\nworld""")");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, UnterminatedTripleQuotedError) {
  auto diags = LexDiagnostics(R"("""no closing triple)");
  EXPECT_TRUE(
      ReportedError(diags, "unterminated triple-quoted string", 1, "5.9"));
}

TEST(LexicalConventionLexing, TripleQuotedLineContinuation) {
  std::string src = "\"\"\"AB\\\nCD\"\"\"";
  auto tokens = Lex(src);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, EmptyTripleQuoted) {
  auto tokens = Lex("\"\"\"\"\"\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// §5.9 is what makes the closing quote obligatory: a string literal is "a
// sequence of characters enclosed by a single pair of double quotes", and
// Syntax 5-3 spells the pair out. The rejection records that clause, and the
// triple-quoted form takes the same one because §5.9 states both.
TEST(LexicalConventionLexing, UnterminatedStringLiteralNames5_9) {
  auto diags = LexDiagnostics("\"never closed");
  EXPECT_TRUE(ReportedError(diags, "unterminated string literal", 1, "5.9"));
}

TEST(LexicalConventionLexing, MultipleStrings) {
  auto tokens = Lex("\"abc\" \"def\"");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"abc\"");
  EXPECT_EQ(tokens[1].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[1].text, "\"def\"");
}

}  // namespace
