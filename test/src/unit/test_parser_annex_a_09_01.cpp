#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AttributeSyntaxParsing, SingleAttrNoValue) {
  auto r = Parse(
      "(* synthesis *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "synthesis");
  EXPECT_EQ(r.cu->modules[0]->attrs[0].value, nullptr);
}

TEST(AttributeSyntaxParsing, SingleAttrWithValue) {
  auto r = Parse(
      "(* depth = 4 *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "depth");
  EXPECT_NE(r.cu->modules[0]->attrs[0].value, nullptr);
}

TEST(AttributeSyntaxParsing, MultipleAttrSpecs) {
  auto r = Parse(
      "(* full_case, parallel_case *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "full_case");
  EXPECT_EQ(r.cu->modules[0]->attrs[1].name, "parallel_case");
}

TEST(AttributeSyntaxParsing, MixedAttrWithAndWithoutValue) {
  auto r = Parse(
      "(* full_case, depth = 8 *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].value, nullptr);
  EXPECT_NE(r.cu->modules[0]->attrs[1].value, nullptr);
}

TEST(AttributeSyntaxParsing, AttrValueConstExpr) {
  auto r = Parse(
      "(* depth = 2 + 2 *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 1u);
  EXPECT_NE(r.cu->modules[0]->attrs[0].value, nullptr);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].value->kind, ExprKind::kBinary);
}

TEST(AttributeSyntaxParsing, AttrOnModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  (* dont_touch *)\n"
      "  logic x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "dont_touch");
}

TEST(AttributeSyntaxParsing, MultipleSeparateAttrInstances) {
  auto r = Parse(
      "module m;\n"
      "  (* full_case *)\n"
      "  (* parallel_case *)\n"
      "  logic x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].name, "full_case");
  EXPECT_EQ(item->attrs[1].name, "parallel_case");
}

TEST(AttributeSyntaxParsing, AttrOnStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* weight = 5 *) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_GE(stmt->attrs.size(), 1u);
  EXPECT_EQ(stmt->attrs[0].name, "weight");
}

TEST(AttributeSyntaxParsing, AttrOnLetPortItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* attr = 5 *) int x) = x;\n"
              "endmodule\n"));
}

TEST(AttributeSyntaxParsing, ThreeAttrSpecs) {
  auto r = Parse(
      "(* a, b = 1, c *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->attrs[0].value, nullptr);
  EXPECT_EQ(r.cu->modules[0]->attrs[1].name, "b");
  EXPECT_NE(r.cu->modules[0]->attrs[1].value, nullptr);
  EXPECT_EQ(r.cu->modules[0]->attrs[2].name, "c");
  EXPECT_EQ(r.cu->modules[0]->attrs[2].value, nullptr);
}

TEST(AttributeSyntaxParsing, AttrOnCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* full_case, parallel_case *)\n"
      "    case (a)\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->attrs.size(), 2u);
}

TEST(AttributeSyntaxParsing, AttrValueStringLiteral) {
  EXPECT_TRUE(ParseOk("(* tool = \"synplify\" *) module m; endmodule\n"));
}

TEST(AttributeSyntaxParsing, AttrNameEscapedIdentifier) {
  auto r = Parse(
      "(* \\full-case *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "full-case");
}

TEST(AttributeSyntaxParsing, ErrorUnterminatedAttribute) {
  EXPECT_FALSE(ParseOk("(* missing_end module m; endmodule\n"));
}

TEST(AttributeSyntaxParsing, ErrorEmptyAttribute) {
  EXPECT_FALSE(ParseOk("(* *) module m; endmodule\n"));
}

TEST(AttributeSyntaxParsing, ErrorTrailingComma) {
  EXPECT_FALSE(ParseOk("(* full_case, *) module m; endmodule\n"));
}

TEST(AttributeSyntaxParsing, ErrorMissingCommaBetweenSpecs) {
  EXPECT_FALSE(ParseOk("(* full_case parallel_case *) module m; endmodule\n"));
}

TEST(AttributeSyntaxParsing, ErrorMissingValueAfterEquals) {
  EXPECT_FALSE(ParseOk("(* depth = *) module m; endmodule\n"));
}

TEST(AttributeSyntaxParsing, AttrNameUnderscoreStart) {
  auto r = Parse(
      "(* _internal = 1 *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "_internal");
}

TEST(AttributeSyntaxParsing, AttrOnPortDeclaration) {
  auto r = Parse(
      "module m((* ramstyle = \"block\" *) input [7:0] a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AttributeSyntaxParsing, AttrInstanceCanBeRepeatedAcrossDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  (* keep *) logic a;\n"
      "  (* keep *) logic b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  ASSERT_GE(items[0]->attrs.size(), 1u);
  ASSERT_GE(items[1]->attrs.size(), 1u);
  EXPECT_EQ(items[0]->attrs[0].name, "keep");
  EXPECT_EQ(items[1]->attrs[0].name, "keep");
}

}  // namespace
