#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(AssertionSemanticsParsing, AssumeProperty) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> ##[1:3] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssumeProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

// §16.14.2: the clause's a1 assumes `req dist {0:=40, 1:=60}`, and a dist
// in an assertion statement is the inside operator over its values, the
// weights being no part of what the property holds for; so the spec's
// boolean is req inside {0, 1}.
TEST(AssertionSemanticsParsing, ADistInAnAssumedBooleanIsReadAsInside) {
  auto r = Parse(
      "module m;\n"
      "  a1: assume property (@(posedge clk) req dist {0:=40, 1:=60});\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  const Expr* boolean = item->body->assert_expr;
  ASSERT_NE(boolean, nullptr);
  EXPECT_EQ(boolean->kind, ExprKind::kInside);
  ASSERT_NE(boolean->lhs, nullptr);
  EXPECT_EQ(boolean->lhs->kind, ExprKind::kIdentifier);
  ASSERT_EQ(boolean->elements.size(), 2u);
  EXPECT_EQ(boolean->elements[0]->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(boolean->elements[1]->kind, ExprKind::kIntegerLiteral);
}

// §16.14.2: a dist_list item may be a value range weighted as a whole,
// `[2:3]:/60`, which is the bracketed range of §11.4.13's inside; and a
// dist in an assert statement is read the same, as inside with the
// weights ignored.
TEST(AssertionSemanticsParsing, ARangeItemOfAnAssertedDistIsAnInsideRange) {
  auto r = Parse(
      "module m;\n"
      "  a1: assert property (@(posedge clk) v dist {1:=40, [2:3]:/60});\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  const Expr* boolean = item->body->assert_expr;
  ASSERT_NE(boolean, nullptr);
  EXPECT_EQ(boolean->kind, ExprKind::kInside);
  ASSERT_EQ(boolean->elements.size(), 2u);
  EXPECT_EQ(boolean->elements[0]->kind, ExprKind::kIntegerLiteral);
  ASSERT_EQ(boolean->elements[1]->kind, ExprKind::kSelect);
  EXPECT_NE(boolean->elements[1]->index, nullptr);
  EXPECT_NE(boolean->elements[1]->index_end, nullptr);
}

// §16.12: the disable condition is an expression_or_dist as well, so a
// property's `disable iff (mode dist {0, 1})` is captured with the inside
// expression as its condition and the implication its body.
TEST(AssertionSemanticsParsing, ADistInADisableConditionIsReadAsInside) {
  auto r = Parse(
      "module m;\n"
      "  property abc(a, b, c);\n"
      "    disable iff (c dist {0, 1}) @(posedge clk) a |=> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* decl = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(decl, nullptr);
  ASSERT_NE(decl->prop_disable_iff, nullptr);
  EXPECT_EQ(decl->prop_disable_iff->kind, ExprKind::kInside);
  EXPECT_EQ(decl->prop_disable_iff->elements.size(), 2u);
  ASSERT_NE(decl->prop_body_tree, nullptr);
  EXPECT_EQ(decl->prop_body_tree->kind, PropertyExprNode::Kind::kImplication);
}

}  // namespace
