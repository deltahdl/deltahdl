#include "fixture_parser.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Parse "initial x = EXPR;" and return the parsed right-hand-side expression
// so the test can inspect how the parser modeled a timescale retrieval call.
const Expr* RhsOf(ParseResult& r) {
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  return item->body->rhs;
}

// Syntax 20-3: $timeunit with no argument is a system-function call.
TEST(TimescaleSystemFunctions, TimeunitParsesWithoutArgument) {
  auto r = Parse("module m; initial x = $timeunit; endmodule");
  const Expr* call = RhsOf(r);
  ASSERT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$timeunit");
  EXPECT_TRUE(call->args.empty());
}

// Syntax 20-3: $timeprecision with no argument is a system-function call.
TEST(TimescaleSystemFunctions, TimeprecisionParsesWithoutArgument) {
  auto r = Parse("module m; initial x = $timeprecision; endmodule");
  const Expr* call = RhsOf(r);
  ASSERT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$timeprecision");
  EXPECT_TRUE(call->args.empty());
}

// Syntax 20-3: the optional argument is a hierarchical identifier.
TEST(TimescaleSystemFunctions, TimeunitParsesHierarchicalArgument) {
  auto r = Parse("module m; initial x = $timeunit(top.dut); endmodule");
  const Expr* call = RhsOf(r);
  ASSERT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$timeunit");
  ASSERT_EQ(call->args.size(), 1u);
}

// The $root argument is accepted as the call argument.
TEST(TimescaleSystemFunctions, TimeprecisionParsesRootArgument) {
  auto r = Parse("module m; initial x = $timeprecision($root); endmodule");
  const Expr* call = RhsOf(r);
  ASSERT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$timeprecision");
  ASSERT_EQ(call->args.size(), 1u);
}

// The $unit compilation-unit-scope argument is the remaining special argument
// form. A bare $unit parses as its own scope system call, so it appears as the
// single argument node the call carries.
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
