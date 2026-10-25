#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

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

// 18.11: randomize() accepts as arguments only names of the calling object's
// properties, which A.8.2 writes as a variable_identifier_list, so an element
// a select picks out of a property is no argument (#8060).
TEST(SubroutineCallExprParsing, PropertySelectArgIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(a, b[0]); end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "randomize() arguments shall be object property "
                            "names, not expressions",
                            2, "18.11"));
}

// 18.11: an expression is no argument of randomize() written bare either.
TEST(SubroutineCallExprParsing, ExpressionArgToTheBareFormIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin randomize(a + 1); end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "randomize() arguments shall be object property "
                            "names, not expressions",
                            2, "18.11"));
}

// 18.11: expressions are not allowed as randomize() arguments. An arithmetic
// expression in the argument list is rejected.
TEST(SubroutineCallExprParsing, ExpressionArgIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(a + 1); end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "randomize() arguments shall be object property "
                            "names, not expressions",
                            2, "18.11"));
}

// 18.11: a literal constant is an expression, not a property name, so it is not
// a valid randomize() argument.
TEST(SubroutineCallExprParsing, LiteralArgIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(5); end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "randomize() arguments shall be object property "
                            "names, not expressions",
                            2, "18.11"));
}

// 18.11: a function call yields a value through computation rather than naming
// a property, so it is an expression and is not an acceptable randomize()
// argument.
TEST(SubroutineCallExprParsing, FunctionCallArgIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(f()); end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "randomize() arguments shall be object property "
                            "names, not expressions",
                            2, "18.11"));
}

}  // namespace
