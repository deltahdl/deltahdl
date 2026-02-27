// Annex A.8.8: Strings

#include "fixture_parser.h"

using namespace delta;

namespace {

static ParseResult Parse(const std::string& src) {
  ParseResult r;
  auto fid = r.mgr.AddFile("<test>", src);
  DiagEngine diag(r.mgr);
  Lexer lexer(r.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, r.arena, diag);
  r.cu = parser.Parse();
  r.has_errors = diag.HasErrors();
  return r;
}

// § string_literal — quoted_string used as primary_literal in assignment
TEST(ParseA88, StringLiteralQuotedStringAsPrimary) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § string_literal — triple_quoted_string used as primary_literal in assignment
TEST(ParseA88, StringLiteralTripleQuotedStringAsPrimary) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\"\"hello\"\"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § quoted_string — contains quoted_string_item (regular ASCII chars)
TEST(ParseA88, QuotedStringWithQuotedStringItems) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"ABC 123 xyz\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § quoted_string — contains string_escape_seq (\any_ASCII_character)
TEST(ParseA88, QuotedStringWithEscapeSeqAnyAscii) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"line1\\nline2\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § quoted_string — contains string_escape_seq
// (\one_to_three_digit_octal_number)
TEST(ParseA88, QuotedStringWithEscapeSeqOctal) {
  auto r = Parse(
      "module m;\n"
      "  byte c;\n"
      "  initial c = \"\\101\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § quoted_string — contains string_escape_seq (\x one_to_two_digit_hex_number)
TEST(ParseA88, QuotedStringWithEscapeSeqHex) {
  auto r = Parse(
      "module m;\n"
      "  byte c;\n"
      "  initial c = \"\\x41\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § triple_quoted_string — contains triple_quoted_string_item (including
// newline)
TEST(ParseA88, TripleQuotedStringItemIncludingNewline) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\"\"line1\nline2\"\"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § triple_quoted_string — contains triple_quoted_string_item (including
// double-quote)
TEST(ParseA88, TripleQuotedStringItemIncludingDoubleQuote) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\"\"say \\\"hi\\\"\"\"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § triple_quoted_string — contains string_escape_seq
TEST(ParseA88, TripleQuotedStringWithEscapeSeq) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\"\"\\n\\t\\\\\"\"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § string_literal — used in $display system task argument
TEST(ParseA88, StringLiteralInSystemTaskArg) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello world\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § string_literal — triple_quoted_string in $display system task argument
TEST(ParseA88, TripleQuotedStringInSystemTaskArg) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"\"\"hello world\"\"\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
