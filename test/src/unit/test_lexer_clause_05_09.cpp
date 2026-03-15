#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, StringLiteralRecognized) {
  auto r = LexOne("\"hello world\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, TripleQuotedStringLiteralRecognized) {
  auto r = LexOne("\"\"\"hello\"\"\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

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
  auto [tokens, errors] = LexWithDiag("\"unterminated");
  EXPECT_TRUE(errors);
}

TEST(LexicalConventionLexing, UnterminatedNewlineError) {
  auto [tokens, errors] = LexWithDiag("\"line1\nline2\"");
  EXPECT_TRUE(errors);
}

TEST(LexicalConventionLexing, LineContinuation) {
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
  auto [tokens, errors] = LexWithDiag(R"("""no closing triple)");
  EXPECT_TRUE(errors);
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

TEST(LexicalConventionLexing, StringWithEscapeSequences) {
  auto r = LexOne("\"line1\\nline2\" ");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
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
