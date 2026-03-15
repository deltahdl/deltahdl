#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, EscapedIdentifierAsName) {
  EXPECT_TRUE(ParseOk("module t; wire \\bus+index ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedKeywordAsIdentifier) {
  EXPECT_TRUE(ParseOk("module t; wire \\module ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedIdentBasic) {
  EXPECT_TRUE(ParseOk("module m; wire \\busa+index ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedIdentKeyword) {
  EXPECT_TRUE(ParseOk("module m; wire \\net ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedIdentSpecialChars) {
  EXPECT_TRUE(ParseOk("module m; wire \\***error-condition*** ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedIdentForwardSlash) {
  EXPECT_TRUE(ParseOk("module m; wire \\net1/\\net2 ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedIdentBraces) {
  EXPECT_TRUE(ParseOk("module m; wire \\{a,b} ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedIdentInExpression) {
  auto r = Parse(
      "module m;\n"
      "  logic \\my-signal ;\n"
      "  initial \\my-signal = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LexicalConventionParsing, EscapedIdentInLetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let \\my+let = 1;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, EscapedIdentifierInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic \\bus+a ;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, EscapedIdentifierPreservesWhitespaceRule) {
  auto r = Parse(
      "module t;\n"
      "  logic \\my+sig ;\n"
      "  assign \\my+sig = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LexicalConventionParsing, EscapedIdentifierAtEndOfDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  logic \\sig! ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LexicalConventionParsing, MultipleEscapedIdentifiers) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic \\a+b , \\c-d ;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, EscapedIdentDashClock) {
  EXPECT_TRUE(ParseOk("module m; wire \\-clock ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedIdentParentheses) {
  EXPECT_TRUE(ParseOk("module m; wire \\a*(b+c) ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedIdentSameAsSimpleIdent) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] cpu3;\n"
      "  assign \\cpu3 = 8'd0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
