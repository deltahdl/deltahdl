#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

static bool LexHasErrors(const std::string& src) {
  SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  return diag.HasErrors();
}

TEST(LexA88, StringLiteralQuotedString) {
  auto tokens = Lex("\"hello\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"hello\"");
}

TEST(LexA88, StringLiteralTripleQuotedString) {
  auto tokens = Lex(R"("""hello""")");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"\"hello\"\"\"");
}

TEST(LexA88, QuotedStringItemRegularAscii) {
  auto tokens = Lex("\"ABC xyz 123 !@#\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"ABC xyz 123 !@#\"");
}

TEST(LexA88, QuotedStringEmpty) {
  auto tokens = Lex("\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"");
}

TEST(LexA88, TripleQuotedStringItemNewline) {
  auto tokens = Lex("\"\"\"line1\nline2\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, TripleQuotedStringItemDoubleQuote) {
  auto tokens = Lex("\"\"\"say \\\"hi\\\"\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, StringEscapeSeqAnyAsciiNamed) {
  auto tokens = Lex("\"\\n\\t\\\\\\\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, StringEscapeSeqAnyAsciiUnknown) {
  auto tokens = Lex("\"\\b\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, StringEscapeSeqOctalOneDigit) {
  auto tokens = Lex("\"\\7\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, StringEscapeSeqOctalTwoDigits) {
  auto tokens = Lex("\"\\77\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, StringEscapeSeqOctalThreeDigits) {
  auto tokens = Lex("\"\\101\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, StringEscapeSeqHexOneDigit) {
  auto tokens = Lex("\"\\xA\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, StringEscapeSeqHexTwoDigits) {
  auto tokens = Lex("\"\\x41\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, TripleQuotedStringEscapeSeq) {
  auto tokens = Lex("\"\"\"\\n\\x41\\101\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(LexA88, QuotedStringUnterminatedError) {
  EXPECT_TRUE(LexHasErrors("\"no closing quote\n"));
}

TEST(LexA88, TripleQuotedStringUnterminatedError) {
  EXPECT_TRUE(LexHasErrors("\"\"\"no closing triple"));
}

TEST(LexA88, TwoConsecutiveStringLiterals) {
  auto tokens = Lex("\"a\" \"b\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStringLiteral);
}

}  // namespace
