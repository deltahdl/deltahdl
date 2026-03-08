#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_2_FreeFormatSingleLine) {
  EXPECT_TRUE(ParseOk("module t; logic a; endmodule"));
}

TEST(ParserClause05, Cl5_2_FreeFormatMultiline) {
  EXPECT_TRUE(
      ParseOk("module\n"
              "  t\n"
              ";\n"
              "  logic\n"
              "    a\n"
              ";\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_2_FreeFormatMaximallyCompact) {

  EXPECT_TRUE(ParseOk("module t;logic a;endmodule"));
}

TEST(ParserClause05, Cl5_2_FreeFormatExcessiveWhitespace) {
  EXPECT_TRUE(ParseOk("  module   t  ;   logic   a  ;   endmodule  "));
}

TEST(ParserClause05, Cl5_2_WhitespaceVariationsProduceSameAST) {
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

TEST(ParserClause05, Cl5_2_AllTokenCategoriesParsed) {
  EXPECT_TRUE(
      ParseOk("module t; // line comment\n"
              "  /* block comment */\n"
              "  logic [7:0] data = 8'hAB;\n"
              "  initial $display(\"hello\");\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_2_EscapedIdentifierPreservesWhitespaceRule) {

  auto r = Parse(
      "module t;\n"
      "  logic \\my+sig ;\n"
      "  assign \\my+sig = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserClause05, Cl5_2_EscapedKeywordAsIdentifier) {

  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic \\module ;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_2_TabsAndFormfeedsAsWhitespace) {
  EXPECT_TRUE(ParseOk("module\tt\f;\flogic\ta\t;\tendmodule"));
}

TEST(ParserClause05, Cl5_2_EmptyModuleBody) {
  EXPECT_TRUE(ParseOk("module t; endmodule"));
}

}
