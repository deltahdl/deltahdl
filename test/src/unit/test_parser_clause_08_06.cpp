// §8.6: Object methods

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.9 — method_call
// =============================================================================
// method_call: method_call_root . method_call_body (no args)
TEST(ParserA609, MethodCallNoArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  ASSERT_NE(expr->lhs, nullptr);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kMemberAccess);
}

// =============================================================================
// A.8.2 Subroutine calls — method_call
// =============================================================================
// § method_call ::= method_call_root . method_call_body
// § method_call_root ::= primary | implicit_class_handle
// Basic method call on identifier
TEST(ParserA82, MethodCallBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  ASSERT_NE(expr->lhs, nullptr);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kMemberAccess);
}

}  // namespace
