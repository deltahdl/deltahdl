#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SubroutineCallSyntaxParsing, MethodCallNoArgs) {
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

TEST(SubroutineCallExprParsing, MethodCallBasic) {
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

TEST(OperatorParsing, MethodCallDotNotation) {
  auto r = Parse(
      "class Packet;\n"
      "  function int current_status();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int status;\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    status = p.current_status();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
