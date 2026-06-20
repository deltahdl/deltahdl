#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprParsing, VariableIdentifierList) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(a, b, c); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

// 18.11: the arguments to randomize() are limited to the names of properties of
// the calling object; a general expression is not allowed. A property selected
// by index is still a property name and remains acceptable.
TEST(SubroutineCallExprParsing, PropertySelectArgIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(a, b[0]); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 18.11: expressions are not allowed as randomize() arguments. An arithmetic
// expression in the argument list is rejected.
TEST(SubroutineCallExprParsing, ExpressionArgIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(a + 1); end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// 18.11: a literal constant is an expression, not a property name, so it is not
// a valid randomize() argument.
TEST(SubroutineCallExprParsing, LiteralArgIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(5); end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// 18.11: a function call yields a value through computation rather than naming
// a property, so it is an expression and is not an acceptable randomize()
// argument.
TEST(SubroutineCallExprParsing, FunctionCallArgIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(f()); end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
