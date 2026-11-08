#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(OptionalScaleParser, ScaleParsesAsSystemCall) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $scale(top.d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* call = r.cu->modules[0]->items[0]->body->rhs;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$scale");
  ASSERT_EQ(call->args.size(), 1u);
  EXPECT_EQ(call->args[0]->kind, ExprKind::kMemberAccess);
}

TEST(OptionalScaleParser, ScaleAcceptsSimpleName) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $scale(d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* call = r.cu->modules[0]->items[0]->body->rhs;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$scale");
  ASSERT_EQ(call->args.size(), 1u);
  EXPECT_EQ(call->args[0]->kind, ExprKind::kIdentifier);
}

}  // namespace
