#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_1_SourceWithAllTokenCategoriesParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [7:0] data = 8'hAB;\n"
              "  initial $display(\"hello\");\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_CommentsDoNotAffectParseResult) {
  auto with = Parse(
      "module /* block */ t; // line\n"
      "  logic a;\n"
      "endmodule\n");
  auto without = Parse(
      "module t;\n"
      "  logic a;\n"
      "endmodule\n");
  ASSERT_NE(with.cu, nullptr);
  ASSERT_NE(without.cu, nullptr);
  EXPECT_FALSE(with.has_errors);
  EXPECT_FALSE(without.has_errors);
  ASSERT_EQ(with.cu->modules.size(), 1u);
  ASSERT_EQ(without.cu->modules.size(), 1u);
  EXPECT_EQ(with.cu->modules[0]->name, without.cu->modules[0]->name);
}

TEST(ParserClause05, Cl5_1_IntegerLiteralInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [31:0] x;\n"
              "  initial x = 32'd42;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_RealLiteralInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  real r;\n"
              "  initial r = 3.14;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_StringLiteralInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"hello world\");\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_TimeLiteralInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial #10ns;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_UnbasedUnsizedLiteralInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [15:0] x;\n"
              "  assign x = '1;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_ArrayLiteralParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int arr [0:1];\n"
              "  initial arr = '{0, 1};\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_StructureLiteralParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } ab_t;\n"
              "  ab_t s;\n"
              "  initial s = '{0, 1};\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_StructureLiteralWithNamedMembersParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } ab_t;\n"
              "  ab_t s;\n"
              "  initial s = '{a:0, b:1};\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_StructureLiteralWithDefaultParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } ab_t;\n"
              "  ab_t s;\n"
              "  initial s = '{default:0};\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_TripleQuotedStringInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"\"\"hello\"\"\");\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_EscapedIdentifierInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic \\bus+a ;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_SystemTaskCallParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $display(\"test\");\n"
              "    $finish;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_SystemFunctionInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [31:0] x;\n"
              "  initial x = $random;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_BuiltinMethodCallParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int q[$];\n"
              "  int sz;\n"
              "  initial sz = q.size();\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_BuiltinMethodCallWithoutParensParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int q[$];\n"
              "  int sz;\n"
              "  initial sz = q.size;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_AttributeOnModuleParses) {
  auto r = Parse(
      "(* synthesis *) module t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->attrs.empty());
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "synthesis");
}

TEST(ParserClause05, Cl5_1_AttributeWithValueParses) {
  auto r = Parse(
      "(* full_case = 1 *) module t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_FALSE(r.cu->modules[0]->attrs.empty());
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "full_case");
  EXPECT_NE(r.cu->modules[0]->attrs[0].value, nullptr);
}

TEST(ParserClause05, Cl5_1_MultipleAttributesOnModule) {
  auto r = Parse(
      "(* synthesis, full_case *) module t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_GE(r.cu->modules[0]->attrs.size(), 2u);
}

TEST(ParserClause05, Cl5_1_AllFourAreasInOneParse) {
  EXPECT_TRUE(
      ParseOk("(* optimize *) module t;\n"
              "  logic [7:0] data = 8'hFF;\n"
              "  real pi = 3.14;\n"
              "  initial begin\n"
              "    $display(\"all areas: %d %f\", data, pi);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_1_UnterminatedAttributeIsError) {
  EXPECT_FALSE(ParseOk("(* missing_end module t; endmodule"));
}

TEST(ParserClause05, Cl5_1_EmptyAttributeIsError) {
  EXPECT_FALSE(ParseOk("(* *) module t; endmodule"));
}

}
