#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_9_EmptyString) {
  auto tokens = Lex("\"\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"");
}

TEST(LexerClause05, Cl5_9_BasicString) {
  auto r = LexOne("\"hello world\" ");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "\"hello world\"");
}

TEST(LexerClause05, Cl5_9_SingleChar) {
  auto r = LexOne("\"A\" ");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "\"A\"");
}

TEST(LexerClause05, Cl5_9_UnterminatedStringError) {
  auto [tokens, errors] = LexWithDiag("\"unterminated");
  EXPECT_TRUE(errors);
}

TEST(LexerClause05, Cl5_9_UnterminatedNewlineError) {
  auto [tokens, errors] = LexWithDiag("\"line1\nline2\"");
  EXPECT_TRUE(errors);
}

TEST(LexerClause05, Cl5_9_LineContinuation) {
  std::string src = "\"AB\\\nCD\"";
  auto tokens = Lex(src);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_9_TripleQuotedBasic) {
  auto tokens = Lex(R"("""hello""")");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_9_TripleQuotedWithNewline) {
  std::string src = "\"\"\"line1\nline2\"\"\"";
  auto tokens = Lex(src);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_9_TripleQuotedWithDoubleQuote) {
  auto tokens = Lex(R"("""say "hello" """)");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_9_TripleQuotedWithEscape) {
  auto tokens = Lex(R"("""hello\nworld""")");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_9_UnterminatedTripleQuotedError) {
  auto [tokens, errors] = LexWithDiag(R"("""no closing triple)");
  EXPECT_TRUE(errors);
}

TEST(LexerClause05, Cl5_9_TripleQuotedLineContinuation) {
  std::string src = "\"\"\"AB\\\nCD\"\"\"";
  auto tokens = Lex(src);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_9_EmptyTripleQuoted) {
  auto tokens = Lex("\"\"\"\"\"\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_9_StringWithEscapeSequences) {
  auto r = LexOne("\"line1\\nline2\" ");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_9_MultipleStrings) {
  auto tokens = Lex("\"abc\" \"def\"");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"abc\"");
  EXPECT_EQ(tokens[1].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[1].text, "\"def\"");
}

}  // namespace
