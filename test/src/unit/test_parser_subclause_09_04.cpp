#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/expr_substitute.h"

using namespace delta;

namespace {

// The actuals of the one property instance asserted in `r`'s module.
template <typename T>
const std::vector<Expr*>* AssertedActuals(T& r) {
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  if (item == nullptr || item->assert_expr == nullptr) return nullptr;
  return &item->assert_expr->args;
}

// Whether `e` is the `or` of an edge event of kind `lhs_edge` over
// `lhs_signal` and the event `rhs`.
bool IsEitherOfEdgeAnd(const Expr* e, TokenKind lhs_edge,
                       std::string_view lhs_signal, const Expr*& rhs) {
  if (e == nullptr || e->kind != ExprKind::kBinary ||
      e->op != TokenKind::kKwOr || e->lhs == nullptr ||
      e->lhs->lhs == nullptr) {
    return false;
  }
  rhs = e->rhs;
  return e->lhs->op == lhs_edge && e->lhs->lhs->text == lhs_signal;
}

// §9.4, footnote 36 to Syntax 9-4: an event expression of comma-separated
// events passed by position is written in parentheses, and the parenthesized
// list is read as one event actual, the `or` of its events, ahead of the
// actual that follows it.
TEST(EventActualParsing, AParenthesizedCommaListIsOneEventActual) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  property p(event e, logic v);\n"
      "    @(e) v;\n"
      "  endproperty\n"
      "  assert property (p((posedge a, negedge b), c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const std::vector<Expr*>* args = AssertedActuals(r);
  ASSERT_NE(args, nullptr);
  ASSERT_EQ(args->size(), 2u);
  const Expr* rhs = nullptr;
  ASSERT_TRUE(IsEitherOfEdgeAnd((*args)[0], TokenKind::kKwPosedge, "a", rhs));
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kKwNegedge);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->text, "b");
  ASSERT_NE((*args)[1], nullptr);
  EXPECT_EQ((*args)[1]->text, "c");
}

// §9.4: a list whose first event has no edge keyword is an event actual
// still where an edge keyword opens a later event, here one in a group nested
// in the list after a `,`, the group's `or` and the list's `,` each read as
// the `or` of the events they join.
TEST(EventActualParsing, AnEdgeLaterInTheListMakesItEvents) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  property p(event e, logic v);\n"
      "    @(e) v;\n"
      "  endproperty\n"
      "  assert property (p((b, (c or negedge d)), a));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const std::vector<Expr*>* args = AssertedActuals(r);
  ASSERT_NE(args, nullptr);
  ASSERT_EQ(args->size(), 2u);
  const Expr* list = (*args)[0];
  ASSERT_NE(list, nullptr);
  EXPECT_EQ(list->kind, ExprKind::kBinary);
  EXPECT_EQ(list->op, TokenKind::kKwOr);
  ASSERT_NE(list->lhs, nullptr);
  EXPECT_EQ(list->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(list->lhs->text, "b");
  const Expr* group = list->rhs;
  ASSERT_NE(group, nullptr);
  EXPECT_EQ(group->kind, ExprKind::kBinary);
  EXPECT_EQ(group->op, TokenKind::kKwOr);
  ASSERT_NE(group->lhs, nullptr);
  EXPECT_EQ(group->lhs->text, "c");
  ASSERT_NE(group->rhs, nullptr);
  EXPECT_EQ(group->rhs->op, TokenKind::kKwNegedge);
  ASSERT_NE((*args)[1], nullptr);
  EXPECT_EQ((*args)[1]->text, "a");
}

// §9.4 with §17.3: a checker's port actual is read the same way, the
// parenthesized list one actual and the expression after it a second; a
// parenthesized signal in the list, `(b)`, which holds no event of its own,
// is the signal.
TEST(EventActualParsing, ACheckerPortTakesAParenthesizedCommaList) {
  auto r = Parse(
      "checker ck(event e, logic v);\n"
      "  a1: assert property (@(e) v);\n"
      "endchecker\n"
      "module m;\n"
      "  logic a, b, c;\n"
      "  ck c1((posedge a, (b)), c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_ports.size(), 2u);
  const Expr* rhs = nullptr;
  ASSERT_TRUE(IsEitherOfEdgeAnd(inst->inst_ports[0].second,
                                TokenKind::kKwPosedge, "a", rhs));
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "b");
  ASSERT_NE(inst->inst_ports[1].second, nullptr);
  EXPECT_EQ(inst->inst_ports[1].second->text, "c");
}

// §9.4: a parenthesized actual in which no edge keyword opens an event is
// left to the reading of an expression, the selects, the parenthesized
// operand and the concatenation with its `,` all within it, so that it is an
// operand and no event.
TEST(EventActualParsing, AParenthesizedExpressionStaysAnExpression) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  logic [1:0] w;\n"
      "  property p(event e, logic v);\n"
      "    @(e) v;\n"
      "  endproperty\n"
      "  assert property (p(posedge a, ((w[1:0]) == {b, c})));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const std::vector<Expr*>* args = AssertedActuals(r);
  ASSERT_NE(args, nullptr);
  ASSERT_EQ(args->size(), 2u);
  ASSERT_NE((*args)[1], nullptr);
  EXPECT_EQ((*args)[1]->property_actual, nullptr);
  EXPECT_FALSE(IsEventActual((*args)[1]));
}

}  // namespace
