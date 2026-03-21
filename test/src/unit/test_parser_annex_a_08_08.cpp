#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StringLiteralSyntaxParsing, StringLiteralQuotedStringAsPrimary) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, StringLiteralTripleQuotedStringAsPrimary) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\"\"hello\"\"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, QuotedStringWithQuotedStringItems) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"ABC 123 xyz\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, QuotedStringWithEscapeSeqAnyAscii) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"line1\\nline2\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, QuotedStringWithEscapeSeqOctal) {
  auto r = Parse(
      "module m;\n"
      "  byte c;\n"
      "  initial c = \"\\101\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, QuotedStringWithEscapeSeqHex) {
  auto r = Parse(
      "module m;\n"
      "  byte c;\n"
      "  initial c = \"\\x41\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, TripleQuotedStringItemIncludingNewline) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\"\"line1\nline2\"\"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, TripleQuotedStringItemIncludingDoubleQuote) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\"\"say \\\"hi\\\"\"\"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, TripleQuotedStringWithEscapeSeq) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\"\"\\n\\t\\\\\"\"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, QuotedStringProducesStringLiteralNode) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(StringLiteralSyntaxParsing, TripleQuotedStringProducesStringLiteralNode) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\"\"hello\"\"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(StringLiteralSyntaxParsing, EmptyQuotedStringProducesStringLiteralNode) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(StringLiteralSyntaxParsing, StringLiteralInSystemTaskArg) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello world\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StringLiteralSyntaxParsing, TripleQuotedStringInSystemTaskArg) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"\"\"hello world\"\"\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
