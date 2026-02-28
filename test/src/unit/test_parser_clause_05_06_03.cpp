// §5.6.3: System tasks and system functions

#include "fixture_parser.h"

using namespace delta;

namespace {

// system_tf_call with empty parentheses
TEST(ParserA609, SystemTfCallEmptyParens) {
  auto r = Parse(
      "module m;\n"
      "  initial $finish();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->callee, "$finish");
  EXPECT_TRUE(expr->args.empty());
}

// system_tf_call with arguments
TEST(ParserA609, SystemTfCallWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial $display(\"x=%0d\", x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->callee, "$display");
  EXPECT_EQ(expr->args.size(), 2u);
}

}  // namespace
