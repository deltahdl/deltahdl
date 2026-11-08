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
