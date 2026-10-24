#include <gtest/gtest.h>

#include <cstddef>
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

// Whether `e` is the `or` of the events `lhs` and `rhs`, neither of which
// an edge keyword opens.
bool IsEitherOfSignals(const Expr* e, std::string_view lhs,
                       std::string_view rhs) {
  return e != nullptr && e->kind == ExprKind::kBinary &&
         e->op == TokenKind::kKwOr && e->lhs != nullptr && e->rhs != nullptr &&
         e->lhs->kind == ExprKind::kIdentifier && e->lhs->text == lhs &&
         e->rhs->kind == ExprKind::kIdentifier && e->rhs->text == rhs;
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

// §9.4, footnote 36 to Syntax 9-4, with §9.4.2: the events of a
// parenthesized list need no edge keyword, so a list of bare signals passed
// by position is one event actual too, the `or` of its events, and not the
// parenthesized operand its first signal would make of it.
TEST(EventActualParsing, AnUnedgedCommaListIsOneEventActual) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  property p(event e, logic v);\n"
      "    @(e) v;\n"
      "  endproperty\n"
      "  assert property (p((a, b), c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const std::vector<Expr*>* args = AssertedActuals(r);
  ASSERT_NE(args, nullptr);
  ASSERT_EQ(args->size(), 2u);
  EXPECT_TRUE(IsEitherOfSignals((*args)[0], "a", "b"));
  ASSERT_NE((*args)[1], nullptr);
  EXPECT_EQ((*args)[1]->text, "c");
}

// §9.4 with §16.11: a parenthesized list of names reads both as an event list
// and as a sequence calling the names after the first at its match, A.8.2
// writing a call's list of arguments as optional, and is read as the event
// list, a scoped or a member's name among them as well. A list holding
// anything else, a sequence before the comma, a literal or an assignment, is
// a sequence with its match items.
TEST(EventActualParsing, OnlyAListOfNamesIsReadAsAnEventList) {
  auto r = Parse(
      "package P; logic b; endpackage\n"
      "module m;\n"
      "  logic a, c;\n"
      "  int x;\n"
      "  property p(e, logic v);\n"
      "    @(e) v;\n"
      "  endproperty\n"
      "  assert property (p((m.a, P::b), c));\n"
      "  assert property (p((a ##1 c, x = 1), c));\n"
      "  assert property (p((1, x = 1), c));\n"
      "  assert property (p((a, x = 1), c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  std::vector<const Expr*> firsts;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kAssertProperty) continue;
    ASSERT_NE(item->assert_expr, nullptr);
    ASSERT_EQ(item->assert_expr->args.size(), 2u);
    firsts.push_back(item->assert_expr->args[0]);
  }
  ASSERT_EQ(firsts.size(), 4u);
  ASSERT_NE(firsts[0], nullptr);
  EXPECT_EQ(firsts[0]->kind, ExprKind::kBinary);
  EXPECT_EQ(firsts[0]->op, TokenKind::kKwOr);
  for (size_t i = 1; i < firsts.size(); ++i) {
    ASSERT_NE(firsts[i], nullptr);
    EXPECT_EQ(firsts[i]->text, "<property_actual>");
  }
}

// §9.4 with §16.10: a parenthesized list holding a select after its comma is
// no sequence, `w[1]` being neither the assignment nor the call a match item
// is, so it is read as the event list it also is, the `or` of its events.
TEST(EventActualParsing, AListNoSequenceReadsIsAnEventList) {
  auto r = Parse(
      "module m;\n"
      "  logic a, c;\n"
      "  logic [1:0] w;\n"
      "  property p(event e, logic v);\n"
      "    @(e) v;\n"
      "  endproperty\n"
      "  assert property (p((a, w[1]), c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const std::vector<Expr*>* args = AssertedActuals(r);
  ASSERT_NE(args, nullptr);
  ASSERT_EQ(args->size(), 2u);
  const Expr* events = (*args)[0];
  ASSERT_NE(events, nullptr);
  EXPECT_TRUE(IsEventActual(events));
  EXPECT_EQ(events->op, TokenKind::kKwOr);
  ASSERT_NE(events->lhs, nullptr);
  EXPECT_EQ(events->lhs->text, "a");
  ASSERT_NE(events->rhs, nullptr);
  EXPECT_EQ(events->rhs->kind, ExprKind::kSelect);
}

// §9.4 with §17.3: a checker's port actual that is a list of bare signals is
// one event actual as well, ahead of the expression after it.
TEST(EventActualParsing, ACheckerPortTakesAnUnedgedCommaList) {
  auto r = Parse(
      "checker ck(event e, logic v);\n"
      "  a1: assert property (@(e) v);\n"
      "endchecker\n"
      "module m;\n"
      "  logic a, b, c;\n"
      "  ck c1((b, a), c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_ports.size(), 2u);
  EXPECT_TRUE(IsEitherOfSignals(inst->inst_ports[0].second, "b", "a"));
  ASSERT_NE(inst->inst_ports[1].second, nullptr);
  EXPECT_EQ(inst->inst_ports[1].second->text, "c");
}

// §16.12.18 beside §9.4: an `iff` in parentheses joins two properties as
// well as guarding an event, and where the parentheses read whole as a
// property_expr, the actual is that property rather than a guarded event.
TEST(EventActualParsing, AParenthesizedIffPropertyStaysAProperty) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  property p(property x, logic v);\n"
      "    v |-> x;\n"
      "  endproperty\n"
      "  assert property (p((a iff b), c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const std::vector<Expr*>* args = AssertedActuals(r);
  ASSERT_NE(args, nullptr);
  ASSERT_EQ(args->size(), 2u);
  ASSERT_NE((*args)[0], nullptr);
  EXPECT_NE((*args)[0]->property_actual, nullptr);
  EXPECT_FALSE(IsEventActual((*args)[0]));
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
