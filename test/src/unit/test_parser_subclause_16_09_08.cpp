#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, FirstMatch) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match(a ##[1:4] b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, FirstMatchWithSequenceMatchItem) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match(a ##[1:4] b, x = e));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, FirstMatchMatchItemGroupingEquivalence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match((a ##[1:4] b, x = e)));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, FirstMatchWithMultipleSequenceMatchItems) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match(a ##[1:4] b, x = e, y = f));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, FirstMatchAsTheAntecedentOfAnImplication) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  assert property (@(posedge clk) first_match(a ##[1:3] b) |-> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* item = r.cu->modules[0]->items.back();
  ASSERT_EQ(item->kind, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item->body, nullptr);
  const PropertyExprNode* tree = item->body->assert_property;
  ASSERT_NE(tree, nullptr);
  EXPECT_EQ(tree->kind, PropertyExprNode::Kind::kImplication);
  ASSERT_NE(tree->sequence, nullptr);
  EXPECT_TRUE(tree->sequence->seq_linear.first_match);
  EXPECT_EQ(tree->sequence->seq_linear.operands.size(), 2u);
}

TEST(AssertionSemanticsParsing, AFirstMatchItemNamingNoVariableIsNotCaptured) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) first_match(a ##1 b, ++);\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "no reading of it gets past this point", 3,
                            "A.2.10"));
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->seq_linear.first_match);
  EXPECT_TRUE(item->seq_linear.operands.empty());
}

}  // namespace
