#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

ModuleItem* FindAssertItem(const ParseResult& r) {
  if (!r.cu || r.cu->modules.size() != 1u) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) return item;
  }
  return nullptr;
}

TEST(AssertionSemanticsParsing, AssertActionBlocks) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    $display(\"PASS\");\n"
      "  else\n"
      "    $error(\"FAIL\");\n"
      "endmodule\n");
  auto* item = FindAssertItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

TEST(AssertionSemanticsParsing, AssertElseClauseOmitted) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    $display(\"PASS\");\n"
      "endmodule\n");
  auto* item = FindAssertItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_EQ(item->assert_fail_stmt, nullptr);
}

TEST(AssertionSemanticsParsing, SimpleConcurrentPropertyCapturesActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a)\n"
      "    $display(\"PASS\");\n"
      "  else\n"
      "    $error(\"FAIL\");\n"
      "endmodule\n");
  auto* item = FindAssertItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_NE(item->body->assert_pass_stmt, nullptr);
  EXPECT_NE(item->body->assert_fail_stmt, nullptr);
}

TEST(AssertionSemanticsParsing, AssertNullStatementActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  auto* item = FindAssertItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
  EXPECT_EQ(item->assert_pass_stmt, nullptr);
  EXPECT_EQ(item->assert_fail_stmt, nullptr);
}

TEST(AssertionSemanticsParsing,
     AClockAfterTheDisableConditionIsTheBodyTreeRootsClock) {
  auto r = Parse(
      "module m;\n"
      "  property abc(a, b, c);\n"
      "    disable iff (a==2) @(posedge clk) not (b ##1 c);\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* decl = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) decl = item;
  }
  ASSERT_NE(decl, nullptr);
  EXPECT_TRUE(decl->prop_clock.empty());
  EXPECT_NE(decl->prop_disable_iff, nullptr);
  ASSERT_NE(decl->prop_body_tree, nullptr);
  EXPECT_EQ(decl->prop_body_tree->kind, PropertyExprNode::Kind::kNot);
  ASSERT_EQ(decl->prop_body_tree->clock.size(), 1u);
  EXPECT_EQ(decl->prop_body_tree->clock[0].edge, Edge::kPosedge);
  ASSERT_EQ(decl->prop_body_tree->operands.size(), 1u);
  EXPECT_EQ(decl->prop_body_tree->operands[0]->kind,
            PropertyExprNode::Kind::kSequence);
}

}  // namespace
