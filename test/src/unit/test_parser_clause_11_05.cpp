// §11.5: Operands

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =========================================================================
// LRM section 11.1 -- Operators and operands overview
// =========================================================================
// --- Primary operand types ---
TEST(ParserSection11, Sec11_1_IdentifierAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = foo;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
}

// --- Call expressions ---
TEST(ParserSection11, Sec11_1_SystemFunctionCallExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$clog2");
}

TEST(ParserSection11, Sec11_1_FunctionCallExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = my_func(a, b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->callee, "my_func");
  EXPECT_EQ(rhs->args.size(), 2u);
}

}  // namespace
