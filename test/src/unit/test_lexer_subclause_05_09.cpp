#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

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

TEST(LexicalConventionLexing, BackslashEndingTheTextLeavesTheStringOpen) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("\"abc\\"),
                            "unterminated string literal", 1, "5.9"));
  EXPECT_TRUE(ReportedError(LexDiagnostics("\"\"\"abc\\"),
                            "unterminated triple-quoted string", 1, "5.9"));
}

TEST(LexicalConventionLexing, TwoQuotesInsideATripleQuotedString) {
  auto tokens = Lex(R"("""a""b""")");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, R"("""a""b""")");
}

}  // namespace
