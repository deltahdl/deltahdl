// Annex A.8.8: Strings

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

// § string_literal — quoted_string form yields kStringLiteral token
TEST(LexA88, StringLiteralQuotedString) {
  auto tokens = Lex("\"hello\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"hello\"");
}

// § string_literal — triple_quoted_string form yields kStringLiteral token
TEST(LexA88, StringLiteralTripleQuotedString) {
  auto tokens = Lex(R"("""hello""")");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"\"hello\"\"\"");
}

// § quoted_string_item — regular ASCII characters (not \, newline, ") allowed
TEST(LexA88, QuotedStringItemRegularAscii) {
  auto tokens = Lex("\"ABC xyz 123 !@#\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"ABC xyz 123 !@#\"");
}

// § quoted_string — empty (zero quoted_string_item) is valid
TEST(LexA88, QuotedStringEmpty) {
  auto tokens = Lex("\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"");
}

// § triple_quoted_string_item — newline is allowed (not excluded like in
// quoted_string)
TEST(LexA88, TripleQuotedStringItemNewline) {
  auto tokens = Lex("\"\"\"line1\nline2\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § triple_quoted_string_item — double-quote allowed inside triple-quoted
// string
TEST(LexA88, TripleQuotedStringItemDoubleQuote) {
  auto tokens = Lex("\"\"\"say \\\"hi\\\"\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § string_escape_seq — \any_ASCII_character form: named escapes
TEST(LexA88, StringEscapeSeqAnyAsciiNamed) {
  // \n, \t, \\, \" are all \any_ASCII_character
  auto tokens = Lex("\"\\n\\t\\\\\\\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § string_escape_seq — \any_ASCII_character form: unknown escape (e.g., \b)
TEST(LexA88, StringEscapeSeqAnyAsciiUnknown) {
  auto tokens = Lex("\"\\b\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § string_escape_seq — \one_to_three_digit_octal_number: one digit
TEST(LexA88, StringEscapeSeqOctalOneDigit) {
  auto tokens = Lex("\"\\7\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § string_escape_seq — \one_to_three_digit_octal_number: two digits
TEST(LexA88, StringEscapeSeqOctalTwoDigits) {
  auto tokens = Lex("\"\\77\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § string_escape_seq — \one_to_three_digit_octal_number: three digits
TEST(LexA88, StringEscapeSeqOctalThreeDigits) {
  auto tokens = Lex("\"\\101\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § string_escape_seq — \x one_to_two_digit_hex_number: one hex digit
TEST(LexA88, StringEscapeSeqHexOneDigit) {
  auto tokens = Lex("\"\\xA\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § string_escape_seq — \x one_to_two_digit_hex_number: two hex digits
TEST(LexA88, StringEscapeSeqHexTwoDigits) {
  auto tokens = Lex("\"\\x41\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § string_escape_seq — escape sequences allowed in triple_quoted_string
TEST(LexA88, TripleQuotedStringEscapeSeq) {
  auto tokens = Lex("\"\"\"\\n\\x41\\101\"\"\"");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// § quoted_string — unterminated (newline terminates the token, reports error)
TEST(LexA88, QuotedStringUnterminatedError) {
  EXPECT_TRUE(LexHasErrors("\"no closing quote\n"));
}

// § triple_quoted_string — unterminated (no closing """) reports error
TEST(LexA88, TripleQuotedStringUnterminatedError) {
  EXPECT_TRUE(LexHasErrors("\"\"\"no closing triple"));
}

// § string_literal — two consecutive string literals are two separate tokens
TEST(LexA88, TwoConsecutiveStringLiterals) {
  auto tokens = Lex("\"a\" \"b\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStringLiteral);
}

}  // namespace
