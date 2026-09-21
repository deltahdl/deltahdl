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

// §11.3.6: the target of an assignment within an expression may be a
// concatenation (§11.4.12), not only a simple variable. The parenthesized form
// with a concatenation left-hand side is admitted by the expression grammar.
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

// §11.3.6: a blocking assignment used within an expression is enclosed in
// parentheses. The parenthesized chain `a = (b = (c = 5))` parses (see
// ChainedAssignInExpr); the same nested assignment without the parentheses is
// not admitted by the expression grammar, so the second `=` stands where the
// statement terminator belongs, and that `=` is what the parser reports under
// §11.3.6 -- the rule broken -- rather than under §12.3 as a missing
// terminator. This observes the rejecting side of the parenthesization rule
// alongside its accepting side.
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

// The shape of sv-tests' 11.3.6--assign_in_expr_inv.sv: two assignments left
// unparenthesized in one statement. The first stray `=` is reported once, the
// rest of the chain is read with it, and the terminator is met where the
// author's statement ends, so nothing after the statement is reported.
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

// §11.3.6 names the mistake the parentheses exist to prevent: `a = b` written
// for `a == b` in a condition. The parenthesized `if ((a = 0))` parses (see
// AssignInExprAsIfCondition); the bare form leaves `=` where the condition's
// closing parenthesis belongs and is reported under §11.3.6 at the `=`.
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

// §11.3.6: a blocking assignment within an expression is permitted only when it
// carries no timing control. An intra-assignment delay inside the parentheses
// is therefore not accepted by the expression grammar.
TEST(OperatorAndExpressionParsing, AssignWithTimingControlInExprIsRejected) {
  auto r = Parse(
      "module t;\n"
      "  int a, b, c;\n"
      "  initial b = (a = #5 c);\n"
      "endmodule\n");
  // The '#' stands where the assignment's right-hand operand belongs, so
  // §11.2's primary report is what fires: §11.3.6 has no report of its own.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

// §11.3.6: an assignment operator is legal in an expression, and §9.4.2's
// event expression is built from expressions, but the assignment forms this
// subclause admits are the parenthesized ones -- a bare assignment in the
// event control is not an expression at all, so it is refused where the event
// control is read.
TEST(OperatorAndExpressionParsing, AssignInEventExpressionIsRejected) {
  auto r = Parse(
      "module t;\n"
      "  logic a, b;\n"
      "  always @(a = b) ;\n"
      "endmodule\n");
  // §9.4.2 owns the event control's closing parenthesis, and that is where the
  // '=' is refused.
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got '='", 3, "9.4.2"));
}

}  // namespace
