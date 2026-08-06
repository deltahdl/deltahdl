#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(OperatorAndExpressionParsing, SignedSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $signed(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$signed");
}

TEST(OperatorAndExpressionParsing, UnsignedSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $unsigned(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$unsigned");
}

TEST(OperatorAndExpressionParsing, SignedWithSubexpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $signed(a + b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$signed");
  EXPECT_EQ(rhs->args.size(), 1u);
  EXPECT_EQ(rhs->args[0]->kind, ExprKind::kBinary);
}

TEST(OperatorAndExpressionParsing, UnsignedInLargerExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $unsigned(a) + $unsigned(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->lhs->callee, "$unsigned");
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->rhs->callee, "$unsigned");
}

TEST(OperatorAndExpressionParsing, SignedWithLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $signed(4'b1100);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$signed");
  EXPECT_EQ(rhs->args.size(), 1u);
}

}  // namespace
