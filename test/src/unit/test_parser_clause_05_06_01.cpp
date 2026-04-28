#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, EscapedIdentifierAsName) {
  EXPECT_TRUE(ParseOk("module t; wire \\bus+index ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedKeywordAsIdentifier) {
  EXPECT_TRUE(ParseOk("module t; wire \\module ; endmodule"));
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

TEST(LexicalConventionParsing, EscapedIdentInHierPath) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  assign x = \\inst .data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LexicalConventionParsing, EscapedIdentAsModuleName) {
  EXPECT_TRUE(ParseOk("module \\my-module ; endmodule\n"));
}

TEST(LexicalConventionParsing, EscapedIdentInPackageScope) {
  auto r = Parse(
      "package \\my-pkg ;\n"
      "  parameter int W = 4;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [\\my-pkg ::W-1:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §5.6.1: escaped identifier accepted as task name (declaration position).
TEST(LexicalConventionParsing, EscapedIdentAsTaskName) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task \\my-task ;\n"
              "  endtask\n"
              "endmodule\n"));
}

// §5.6.1: escaped identifier accepted as function name.
TEST(LexicalConventionParsing, EscapedIdentAsFunctionName) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int \\f+1 ();\n"
              "    return 0;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// §5.6.1: digit-leading body is legal as escaped identifier (illegal as simple).
TEST(LexicalConventionParsing, EscapedIdentAllDigits) {
  EXPECT_TRUE(ParseOk("module m; logic \\1234 ; endmodule"));
}

}  // namespace
