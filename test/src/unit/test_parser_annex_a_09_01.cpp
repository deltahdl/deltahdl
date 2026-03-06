#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §A.9.1 — attribute_instance: (* attr_spec { , attr_spec } *)

TEST(ParserA91, SingleAttrNoValue) {
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

TEST(ParserA91, SingleAttrWithValue) {
  auto r = Parse(
      "(* depth = 4 *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "depth");
  EXPECT_NE(r.cu->modules[0]->attrs[0].value, nullptr);
}

TEST(ParserA91, MultipleAttrSpecs) {
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

TEST(ParserA91, MixedAttrWithAndWithoutValue) {
  auto r = Parse(
      "(* full_case, depth = 8 *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].value, nullptr);
  EXPECT_NE(r.cu->modules[0]->attrs[1].value, nullptr);
}

TEST(ParserA91, AttrValueConstExpr) {
  auto r = Parse(
      "(* depth = 2 + 2 *)\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->attrs.size(), 1u);
  EXPECT_NE(r.cu->modules[0]->attrs[0].value, nullptr);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].value->kind, ExprKind::kBinary);
}

TEST(ParserA91, AttrOnModuleItem) {
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

TEST(ParserA91, MultipleSeparateAttrInstances) {
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

TEST(ParserA91, AttrOnStatement) {
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

TEST(ParserA91, AttrOnLetPortItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* attr = 5 *) int x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA91, ThreeAttrSpecs) {
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

TEST(ParserA91, AttrOnCaseStatement) {
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

TEST(ParserA91, AttrValueStringLiteral) {
  EXPECT_TRUE(
      ParseOk("(* tool = \"synplify\" *) module m; endmodule\n"));
}

}  // namespace
