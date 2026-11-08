#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

const Expr* RhsOf(const ParseResult& r) {
  return r.cu->modules[0]->items[0]->body->rhs;
}

TEST(MinTypMaxParse, TripletBuildsThreeOrderedExprs) {
  auto r = Parse("module t; initial x = (10:20:30); endmodule");
  ASSERT_FALSE(r.has_errors);
  const Expr* e = RhsOf(r);
  ASSERT_EQ(e->kind, ExprKind::kMinTypMax);
  ASSERT_NE(e->lhs, nullptr);
  ASSERT_NE(e->condition, nullptr);
  ASSERT_NE(e->rhs, nullptr);
  EXPECT_EQ(e->lhs->int_val, 10u);
  EXPECT_EQ(e->condition->int_val, 20u);
  EXPECT_EQ(e->rhs->int_val, 30u);
}

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

TEST(MinTypMaxParse, SingleValueIsNotTriplet) {
  auto r = Parse("module t; initial x = (7); endmodule");
  ASSERT_FALSE(r.has_errors);
  const Expr* e = RhsOf(r);
  EXPECT_NE(e->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(e->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(e->int_val, 7u);
}

TEST(MinTypMaxParse, RejectsMissingMaxExpression) {
  auto r = Parse("module t; initial x = (1:2); endmodule");
  EXPECT_TRUE(ReportedError(r.diags, "expected ':', got ')'", 1, "11.11"));
}

TEST(MinTypMaxParse, RejectsFourthValue) {
  auto r = Parse("module t; initial x = (1:2:3:4); endmodule");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ':'", 1, "11.11"));
}

}  // namespace
