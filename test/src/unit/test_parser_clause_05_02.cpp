#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, FreeFormatSingleLine) {
  EXPECT_TRUE(ParseOk("module t; logic a; endmodule"));
}

TEST(LexicalConventionParsing, FreeFormatMultiline) {
  EXPECT_TRUE(
      ParseOk("module\n"
              "  t\n"
              ";\n"
              "  logic\n"
              "    a\n"
              ";\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, FreeFormatMaximallyCompact) {
  EXPECT_TRUE(ParseOk("module t;logic a;endmodule"));
}

TEST(LexicalConventionParsing, FreeFormatExcessiveWhitespace) {
  EXPECT_TRUE(ParseOk("  module   t  ;   logic   a  ;   endmodule  "));
}

TEST(LexicalConventionParsing, WhitespaceVariationsProduceSameAST) {
  auto compact = Parse("module t;logic a;assign a=1'b0;endmodule");
  auto spread = Parse(
      "module\n  t\n;\n  logic\n  a\n;\n  assign\n  a\n=\n1'b0\n;\n"
      "endmodule\n");
  ASSERT_NE(compact.cu, nullptr);
  ASSERT_NE(spread.cu, nullptr);
  EXPECT_FALSE(compact.has_errors);
  EXPECT_FALSE(spread.has_errors);
  ASSERT_EQ(compact.cu->modules.size(), 1u);
  ASSERT_EQ(spread.cu->modules.size(), 1u);
  EXPECT_EQ(compact.cu->modules[0]->name, spread.cu->modules[0]->name);
}

TEST(LexicalConventionParsing, SourceWithAllTokenCategoriesParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [7:0] data = 8'hAB;\n"
              "  initial $display(\"hello\");\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, AllTokenCategoriesParsed) {
  EXPECT_TRUE(
      ParseOk("module t; // line comment\n"
              "  /* block comment */\n"
              "  logic [7:0] data = 8'hAB;\n"
              "  initial $display(\"hello\");\n"
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

TEST(LexicalConventionParsing, EscapedKeywordAsIdentifier) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic \\module ;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, TabsAndFormfeedsAsWhitespace) {
  EXPECT_TRUE(ParseOk("module\tt\f;\flogic\ta\t;\tendmodule"));
}

TEST(LexicalConventionParsing, EmptyModuleBody) {
  EXPECT_TRUE(ParseOk("module t; endmodule"));
}

TEST(LexicalConventionParsing, BlockCommentAsSeparatorParses) {
  EXPECT_TRUE(ParseOk("module/**/t;logic/**/a;endmodule"));
}

TEST(LexicalConventionParsing, CrlfLineEndingsParseCorrectly) {
  EXPECT_TRUE(
      ParseOk("module t;\r\n  logic a;\r\n  assign a = 1'b0;\r\nendmodule\r\n"));
}

TEST(LexicalConventionParsing, CarriageReturnAloneAsWhitespace) {
  EXPECT_TRUE(ParseOk("module\rt\r;\rlogic\ra\r;\rendmodule"));
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

TEST(LexicalConventionParsing, LineCommentBetweenTokens) {
  EXPECT_TRUE(
      ParseOk("module // comment\n"
              "t // comment\n"
              "; // comment\n"
              "endmodule // comment\n"));
}

}  // namespace
