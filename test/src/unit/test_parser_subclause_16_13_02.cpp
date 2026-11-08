#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(AssertionDeclParsing, PropertyExpr_MulticlockedOverlappingImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) a |-> @(posedge clk2) b);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, MultichannelAssertPropertyInline) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk1) a ##1 @(posedge clk2) b\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, MulticlockedNonoverlappingImplicationInPropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p_multi;\n"
      "    @(posedge clk1) req |=> @(posedge clk2) ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, MulticlockedBooleanAndOfClockedOperands) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    (@(posedge clk0) sig0) and (@(posedge clk1) sig1)\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, MulticlockedIfElseProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk0) if (b) @(posedge clk1) s1\n"
      "    else @(posedge clk2) s2\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, MulticlockedImplicationWithBooleanAndConsequent) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk0) s0 |=>\n"
      "      (@(posedge clk1) s1) and (@(posedge clk2) s2)\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, AClockBeforeAnOperandIsRecordedOnItsNode) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk0) sig0 |=> @(posedge clk1) sig1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  const PropertyExprNode* root = item->body->assert_property;
  ASSERT_NE(root, nullptr);
  EXPECT_EQ(root->kind, PropertyExprNode::Kind::kImplication);
  EXPECT_TRUE(root->strong);
  ASSERT_EQ(root->operands.size(), 1u);
  const PropertyExprNode* consequent = root->operands[0];
  EXPECT_EQ(consequent->kind, PropertyExprNode::Kind::kBoolean);
  ASSERT_EQ(consequent->clock.size(), 1u);
  EXPECT_EQ(consequent->clock[0].edge, Edge::kPosedge);
  ASSERT_NE(consequent->clock[0].signal, nullptr);
  EXPECT_EQ(consequent->clock[0].signal->text, "clk1");
  ASSERT_NE(consequent->boolean, nullptr);
  EXPECT_EQ(consequent->boolean->text, "sig1");
}

TEST(AssertionParsing, AParenthesisedClockedOperandIsAPropertyOperand) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk0)\n"
      "    (@(posedge clk0) sig0) and (@(posedge clk1) sig1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  const PropertyExprNode* root = item->body->assert_property;
  ASSERT_NE(root, nullptr);
  EXPECT_EQ(root->kind, PropertyExprNode::Kind::kAnd);
  ASSERT_EQ(root->operands.size(), 2u);
  EXPECT_EQ(root->operands[0]->kind, PropertyExprNode::Kind::kBoolean);
  ASSERT_EQ(root->operands[0]->clock.size(), 1u);
  EXPECT_EQ(root->operands[0]->clock[0].signal->text, "clk0");
  ASSERT_EQ(root->operands[1]->clock.size(), 1u);
  EXPECT_EQ(root->operands[1]->clock[0].signal->text, "clk1");
}

}  // namespace
