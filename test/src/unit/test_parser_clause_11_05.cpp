#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(OperatorAndExpressionParsing, IdentifierAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = foo;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
}

TEST(OperatorAndExpressionParsing, SystemFunctionCallExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$clog2");
}

TEST(OperatorAndExpressionParsing, FunctionCallExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = my_func(a, b);\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->callee, "my_func");
  EXPECT_EQ(rhs->args.size(), 2u);
}

}  // namespace
