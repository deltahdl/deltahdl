#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

const Expr* RhsOf(ParseResult& r) {
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  return item->body->rhs;
}

TEST(TimescaleSystemFunctions, TimeunitParsesWithoutArgument) {
  auto r = Parse("module m; initial x = $timeunit; endmodule");
  const Expr* call = RhsOf(r);
  ASSERT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$timeunit");
  EXPECT_TRUE(call->args.empty());
}

TEST(TimescaleSystemFunctions, TimeprecisionParsesWithoutArgument) {
  auto r = Parse("module m; initial x = $timeprecision; endmodule");
  const Expr* call = RhsOf(r);
  ASSERT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$timeprecision");
  EXPECT_TRUE(call->args.empty());
}

TEST(TimescaleSystemFunctions, TimeunitParsesHierarchicalArgument) {
  auto r = Parse("module m; initial x = $timeunit(top.dut); endmodule");
  const Expr* call = RhsOf(r);
  ASSERT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$timeunit");
  ASSERT_EQ(call->args.size(), 1u);
}

TEST(TimescaleSystemFunctions, TimeprecisionParsesRootArgument) {
  auto r = Parse("module m; initial x = $timeprecision($root); endmodule");
  const Expr* call = RhsOf(r);
  ASSERT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$timeprecision");
  ASSERT_EQ(call->args.size(), 1u);
}

TEST(TimescaleSystemFunctions, TimeunitParsesUnitArgument) {
  auto r = Parse("module m; initial x = $timeunit($unit); endmodule");
  const Expr* call = RhsOf(r);
  ASSERT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$timeunit");
  ASSERT_EQ(call->args.size(), 1u);
  ASSERT_EQ(call->args[0]->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->args[0]->callee, "$unit");
}

}  // namespace
