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

TEST(Parser, ClassWithMethod) {
  auto r = Parse(
      "class pkt;\n"
      "  function int get_data();\n"
      "    return data;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_NE(cls->members[0]->method, nullptr);
}

}  // namespace
