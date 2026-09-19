#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

// §16.12.1 has an instance of a named property stand as a property_spec, so
// `assert property (p_base)` is evaluated as the body of p_base would be in
// its place. The three cases at the end read what the parser keeps for that
// substitution: the body's leading clock and boolean on the declaration, and
// the instance's name on the assertion, with no report of its own, since only
// the elaborator can tell the name of a property from the name of a variable.

const ModuleItem* FindAssertProperty(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) return item;
  }
  return nullptr;
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

const ModuleItem* FindPropertyDecl(ParseResult& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl && item->name == name) {
      return item;
    }
  }
  return nullptr;
}

bool RefersToInstance(const ModuleItem* decl, std::string_view name) {
  for (auto ref : decl->prop_instance_refs) {
    if (ref == name) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, PropertyReference) {
  auto r = Parse(
      "module m;\n"
      "  property p_base;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p_base);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.12.1: an instance of a named property may be used not only as a
// top-level property_spec (see PropertyReference above) but also as a
// property_expr — that is, as the operand of a property-building operator.
// Here `leaf` is instantiated as the operand of `not` inside `outer`; the
// parser accepts that property_expr position and records the instance among
// the declaring property's instance references.
TEST(AssertionSemanticsParsing, PropertyInstanceUsedAsPropertyExprOperand) {
  auto r = Parse(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  property outer;\n"
      "    @(posedge clk) not leaf();\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* outer = FindPropertyDecl(r, "outer");
  ASSERT_NE(outer, nullptr);
  EXPECT_TRUE(RefersToInstance(outer, "leaf"));
}

// A property whose body is a leading clocking event and a boolean is the form
// an assertion written in place of its instance is evaluated in, so the parser
// keeps the clock and the boolean. The boolean here is a disjunction, so a
// capture that stopped at the first operand would keep an expression of a
// different kind.
TEST(AssertionSemanticsParsing, ClockedBooleanPropertyBodyIsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  property req_only_when_enabled;\n"
      "    @(posedge clk) !req || en;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* decl = FindPropertyDecl(r, "req_only_when_enabled");
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->prop_clock.size(), 1u);
  EXPECT_EQ(decl->prop_clock[0].edge, Edge::kPosedge);
  ASSERT_NE(decl->prop_body_expr, nullptr);
  EXPECT_EQ(decl->prop_body_expr->kind, ExprKind::kBinary);
}

// A body holding an implication is a temporal property_spec rather than the
// clocked boolean form, so the parser keeps its clock and the tree of
// operands an assertion's spec is read into (§16.12.17), and no boolean: an
// instance of this property is the root of the instantiating assertion's
// tree.
TEST(AssertionSemanticsParsing, TemporalPropertyBodyIsCapturedAsATree) {
  auto r = Parse(
      "module m;\n"
      "  property p_base;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* decl = FindPropertyDecl(r, "p_base");
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->prop_clock.size(), 1u);
  EXPECT_EQ(decl->prop_clock[0].edge, Edge::kPosedge);
  EXPECT_EQ(decl->prop_body_expr, nullptr);
  ASSERT_NE(decl->prop_body_tree, nullptr);
  EXPECT_EQ(decl->prop_body_tree->kind, PropertyExprNode::Kind::kImplication);
}

// An assertion whose whole property_spec is one name is an instance of a
// named property when the name is a property's. The parser records the name
// and reports nothing, leaving the substitution and the report to the
// elaborator.
TEST(AssertionSemanticsParsing, PropertyInstanceSpecIsRecordedUnreported) {
  auto r = Parse(
      "module m;\n"
      "  property p_base;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "  assert property (p_base) x = 1; else x = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* assertion = FindAssertProperty(r);
  ASSERT_NE(assertion, nullptr);
  EXPECT_EQ(assertion->prop_instance_name, "p_base");
  EXPECT_EQ(assertion->body, nullptr);
  ASSERT_NE(assertion->assert_pass_stmt, nullptr);
  ASSERT_NE(assertion->assert_fail_stmt, nullptr);
  EXPECT_TRUE(r.diags.empty());
}

}  // namespace
