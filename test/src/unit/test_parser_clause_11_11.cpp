#include "fixture_parser.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Navigate `module t; initial x = <expr>; endmodule` down to the RHS of the
// blocking assignment, so a test can inspect how <expr> parsed.
const Expr* RhsOf(const ParseResult& r) {
  return r.cu->modules[0]->items[0]->body->rhs;
}

// §11.11 / Syntax 11-7 mintypmax_expression: a colon-separated triplet in
// parentheses parses to a single min:typ:max node holding all three
// expressions in min, typ, max order.
TEST(MinTypMaxParse, TripletBuildsThreeOrderedExprs) {
  auto r = Parse("module t; initial x = (10:20:30); endmodule");
  ASSERT_FALSE(r.has_errors);
  const Expr* e = RhsOf(r);
  ASSERT_EQ(e->kind, ExprKind::kMinTypMax);
  ASSERT_NE(e->lhs, nullptr);
  ASSERT_NE(e->condition, nullptr);
  ASSERT_NE(e->rhs, nullptr);
  EXPECT_EQ(e->lhs->int_val, 10u);        // min
  EXPECT_EQ(e->condition->int_val, 20u);  // typ
  EXPECT_EQ(e->rhs->int_val, 30u);        // max
}

// §11.11 "used wherever expressions can appear" (Example 1): two parenthesized
// triplets combined by a binary operator. Each operand must parse as its own
// mintypmax node — the general parenthesized-primary path recognizes the form,
// not just the delay positions.
TEST(MinTypMaxParse, TripletsAsBinaryOperands) {
  auto r = Parse("module t; initial x = (1:2:3) + (4:5:6); endmodule");
  ASSERT_FALSE(r.has_errors);
  const Expr* e = RhsOf(r);
  ASSERT_EQ(e->kind, ExprKind::kBinary);
  EXPECT_EQ(e->op, TokenKind::kPlus);
  ASSERT_EQ(e->lhs->kind, ExprKind::kMinTypMax);
  ASSERT_EQ(e->rhs->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(e->lhs->lhs->int_val, 1u);
  EXPECT_EQ(e->lhs->condition->int_val, 2u);
  EXPECT_EQ(e->lhs->rhs->int_val, 3u);
  EXPECT_EQ(e->rhs->lhs->int_val, 4u);
  EXPECT_EQ(e->rhs->condition->int_val, 5u);
  EXPECT_EQ(e->rhs->rhs->int_val, 6u);
}

// §11.11 Example 2 shape: a triplet mixed with a plain (non-triplet) operand.
// Only the triplet operand becomes a mintypmax node.
TEST(MinTypMaxParse, TripletMixedWithPlainOperand) {
  auto r = Parse("module t; initial x = 200 - (50:75:100); endmodule");
  ASSERT_FALSE(r.has_errors);
  const Expr* e = RhsOf(r);
  ASSERT_EQ(e->kind, ExprKind::kBinary);
  EXPECT_EQ(e->op, TokenKind::kMinus);
  EXPECT_EQ(e->lhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(e->lhs->int_val, 200u);
  ASSERT_EQ(e->rhs->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(e->rhs->lhs->int_val, 50u);
  EXPECT_EQ(e->rhs->condition->int_val, 75u);
  EXPECT_EQ(e->rhs->rhs->int_val, 100u);
}

// mintypmax_expression's first alternative is a bare expression: a single
// parenthesized value is NOT a mintypmax node, just a parenthesized primary.
TEST(MinTypMaxParse, SingleValueIsNotTriplet) {
  auto r = Parse("module t; initial x = (7); endmodule");
  ASSERT_FALSE(r.has_errors);
  const Expr* e = RhsOf(r);
  EXPECT_NE(e->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(e->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(e->int_val, 7u);
}

// Negative form: the triplet requires exactly two colons. A single colon
// (min:typ with no max) is rejected.
TEST(MinTypMaxParse, RejectsMissingMaxExpression) {
  EXPECT_FALSE(ParseOk("module t; initial x = (1:2); endmodule"));
}

// Negative form: a fourth colon-separated value is not part of the grammar.
TEST(MinTypMaxParse, RejectsFourthValue) {
  EXPECT_FALSE(ParseOk("module t; initial x = (1:2:3:4); endmodule"));
}

}  // namespace
