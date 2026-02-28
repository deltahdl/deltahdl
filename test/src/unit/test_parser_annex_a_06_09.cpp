// Annex A.6.9: Subroutine call statements

#include "fixture_parser.h"

using namespace delta;

namespace {

// tf_call with single argument
TEST(ParserA609, TfCallSingleArg) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(42); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->args.size(), 1u);
}

}  // namespace
