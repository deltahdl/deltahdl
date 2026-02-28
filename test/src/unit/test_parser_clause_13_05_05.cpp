// §13.5.5: Optional argument list

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.9 Subroutine call statements — subroutine_call_statement
// =============================================================================
// --- subroutine_call_statement: subroutine_call ; ---
// tf_call with empty parentheses
TEST(ParserA609, TfCallEmptyParens) {
  auto r = Parse(
      "module m;\n"
      "  task foo; endtask\n"
      "  initial foo();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->callee, "foo");
  EXPECT_TRUE(expr->args.empty());
}

}  // namespace
