#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, EscapedIdentifierAsName) {
  EXPECT_TRUE(ParseOk("module t; wire \\bus+index ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedKeywordAsIdentifier) {
  EXPECT_TRUE(ParseOk("module t; wire \\module ; endmodule"));
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

TEST(LexicalConventionParsing, EscapedIdentAsTaskName) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task \\my-task ;\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, EscapedIdentAsFunctionName) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int \\f+1 ();\n"
              "    return 0;\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, EscapedIdentAllDigits) {
  EXPECT_TRUE(ParseOk("module m; logic \\1234 ; endmodule"));
}

TEST(LexicalConventionParsing, EscapedIdentifierAstNameIsStripped) {
  auto r = Parse("module m; logic \\bus+index ; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "bus+index");
}

TEST(LexicalConventionParsing, EscapedAndSimpleIdentifierShareAstName) {
  auto escaped = Parse("module m; logic \\cpu3 ; endmodule");
  auto simple = Parse("module m; logic cpu3; endmodule");
  ASSERT_NE(escaped.cu, nullptr);
  ASSERT_NE(simple.cu, nullptr);
  auto* esc_item = FirstItem(escaped);
  auto* sim_item = FirstItem(simple);
  ASSERT_NE(esc_item, nullptr);
  ASSERT_NE(sim_item, nullptr);
  EXPECT_EQ(esc_item->name, sim_item->name);
  EXPECT_EQ(esc_item->name, "cpu3");
}

}  // namespace
