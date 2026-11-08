#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;
namespace {

TEST(OperatorAndExpressionParsing, CompoundAssignInExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial b = (a += 1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, ChainedAssignInExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial a = (b = (c = 5));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, AllCompoundAssignOpsInExpr) {
  auto r = Parse(
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    b = (a -= 1);\n"
      "    b = (a *= 2);\n"
      "    b = (a /= 2);\n"
      "    b = (a %= 3);\n"
      "    b = (a &= 8'hFF);\n"
      "    b = (a |= 8'h01);\n"
      "    b = (a ^= 8'hAA);\n"
      "    b = (a <<= 1);\n"
      "    b = (a >>= 1);\n"
      "    b = (a <<<= 1);\n"
      "    b = (a >>>= 1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, AssignInExprAsIfCondition) {
  auto r = Parse(
      "module t;\n"
      "  int a;\n"
      "  initial if ((a = 0)) ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kEq);
}

TEST(OperatorAndExpressionParsing, ConcatTargetAssignInExpr) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] q;\n"
      "  initial q = ({a, b} = 8'hAB);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, UnparenthesizedAssignInExprIsRejected) {
  auto r = Parse(
      "module t;\n"
      "  int a, b, c;\n"
      "  initial a = b = c;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "an assignment within an expression must be enclosed in parentheses", 3,
      "11.3.6"));
  EXPECT_FALSE(ReportedError(r.diags, "expected ';', got '='", 3, "12.3"));
}

TEST(OperatorAndExpressionParsing, ChainOfUnparenthesizedAssignsReportedOnce) {
  auto r = Parse(
      "module t;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    a = b = c = 5;\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "an assignment within an expression must be enclosed in parentheses", 4,
      "11.3.6"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(OperatorAndExpressionParsing, UnparenthesizedAssignAsIfConditionRejected) {
  auto r = Parse(
      "module t;\n"
      "  int a, b;\n"
      "  initial if (a = b) ;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "an assignment within an expression must be enclosed in parentheses", 3,
      "11.3.6"));
  EXPECT_FALSE(ReportedError(r.diags, "expected ')', got '='", 3, "12.4"));
}

TEST(OperatorAndExpressionParsing, AssignWithTimingControlInExprIsRejected) {
  auto r = Parse(
      "module t;\n"
      "  int a, b, c;\n"
      "  initial b = (a = #5 c);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(OperatorAndExpressionParsing, AssignInEventExpressionIsRejected) {
  auto r = Parse(
      "module t;\n"
      "  logic a, b;\n"
      "  always @(a = b) ;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got '='", 3, "9.4.2"));
}

}  // namespace
