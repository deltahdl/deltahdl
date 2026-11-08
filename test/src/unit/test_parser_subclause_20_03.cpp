#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"

using namespace delta;
namespace {

TEST(TimeFunctionSyntax, TimeAlternativeParses) {
  auto r = Parse(
      "module m;\n"
      "  integer t;\n"
      "  initial t = $time;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$time");
  EXPECT_TRUE(rhs->args.empty());
}

TEST(TimeFunctionSyntax, StimeAlternativeParses) {
  auto r = Parse(
      "module m;\n"
      "  integer t;\n"
      "  initial t = $stime;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$stime");
  EXPECT_TRUE(rhs->args.empty());
}

TEST(TimeFunctionSyntax, RealtimeAlternativeParses) {
  auto r = Parse(
      "module m;\n"
      "  real t;\n"
      "  initial t = $realtime;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$realtime");
  EXPECT_TRUE(rhs->args.empty());
}

TEST(TimeFunctionSyntax, TimeFunctionAsExpressionOperand) {
  auto r = Parse(
      "module m;\n"
      "  integer t;\n"
      "  initial t = $time + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->lhs->callee, "$time");
}

TEST(TimeFunctionSyntax, TimeFunctionAsCallArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $display($time);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* call = FirstInitialExpr(r);
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$display");
  ASSERT_EQ(call->args.size(), 1u);
  EXPECT_EQ(call->args[0]->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->args[0]->callee, "$time");
}

TEST(TimeFunctionSyntax, PlainIdentifierIsNotTimeFunction) {
  auto r = Parse(
      "module m;\n"
      "  integer stime;\n"
      "  integer t;\n"
      "  initial t = stime;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_NE(rhs->kind, ExprKind::kSystemCall);
}

}  // namespace
