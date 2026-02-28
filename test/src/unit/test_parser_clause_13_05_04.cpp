// §13.5.4: Argument binding by name

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.9 — list_of_arguments (named)
// =============================================================================
// All named arguments
TEST(ParserA609, ListOfArgsAllNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(.a(1), .b(2)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->arg_names.size(), 2u);
  EXPECT_EQ(expr->arg_names[0], "a");
  EXPECT_EQ(expr->arg_names[1], "b");
  EXPECT_EQ(expr->args.size(), 2u);
}

}  // namespace
