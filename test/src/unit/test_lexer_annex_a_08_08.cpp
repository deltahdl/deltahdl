#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StringLiteralLexing, StringLiteralQuotedString) {
  auto tokens = Lex("\"hello\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"hello\"");
}

TEST(StringLiteralLexing, StringLiteralTripleQuotedString) {
  auto tokens = Lex(R"("""hello""")");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"\"hello\"\"\"");
}

TEST(StringLiteralLexing, QuotedStringItemRegularAscii) {
  auto tokens = Lex("\"ABC xyz 123 !@#\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"ABC xyz 123 !@#\"");
}

TEST(StringLiteralLexing, QuotedStringEmpty) {
  auto tokens = Lex("\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"");
}

TEST(StringLiteralLexing, TripleQuotedStringItemNewline) {
  auto tokens = Lex("\"\"\"line1\nline2\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, TripleQuotedStringItemDoubleQuote) {
  auto tokens = Lex("\"\"\"A\"B\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"\"A\"B\"\"\"");
}

TEST(StringLiteralLexing, StringEscapeSeqAnyAsciiNamed) {
  auto tokens = Lex("\"\\n\\t\\\\\\\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, StringEscapeSeqAnyAsciiUnknown) {
  auto tokens = Lex("\"\\b\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, StringEscapeSeqOctalOneDigit) {
  auto tokens = Lex("\"\\7\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, StringEscapeSeqOctalTwoDigits) {
  auto tokens = Lex("\"\\77\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, StringEscapeSeqOctalThreeDigits) {
  auto tokens = Lex("\"\\101\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, StringEscapeSeqHexOneDigit) {
  auto tokens = Lex("\"\\xA\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, StringEscapeSeqHexTwoDigits) {
  auto tokens = Lex("\"\\x41\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, TripleQuotedStringEscapeSeq) {
  auto tokens = Lex("\"\"\"\\n\\x41\\101\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, TripleQuotedStringUnterminatedError) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("\"\"\"no closing triple"),
                            "unterminated triple-quoted string", 1, "5.9"));
}

TEST(StringLiteralLexing, TwoConsecutiveStringLiterals) {
  auto tokens = Lex("\"a\" \"b\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, QuotedStringItemTabCharacter) {
  auto tokens = Lex("\"hello\tworld\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, TripleQuotedStringEmpty) {
  auto tokens = Lex("\"\"\"\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(StringLiteralLexing, QuotedStringNewlineTerminatesError) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("\"before\nafter\""),
                            "unterminated string literal", 1, "5.9"));
}

TEST(StringLiteralLexing, QuotedStringUnterminatedAtEofError) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("\"no close quote"),
                            "unterminated string literal", 1, "5.9"));
}

TEST(StringLiteralLexing, TripleQuotedStringPartialCloseError) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("\"\"\"only two closing quotes\"\""),
                            "unterminated triple-quoted string", 1, "5.9"));
}

TEST(StringLiteralLexing, QuotedStringCarriageReturnTerminatesError) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("\"before\rafter\""),
                            "unterminated string literal", 1, "5.9"));
}

}  // namespace
