#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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

// §11.3.6: a blocking assignment used within an expression shall be enclosed in
// parentheses. The parenthesized chain `a = (b = (c = 5))` parses (see
// ChainedAssignInExpr); the same nested assignment without the parentheses is
// not admitted by the expression grammar, so the embedded `=` is left over and
// the statement fails to parse. This observes the rejecting side of the
// parenthesization rule alongside its accepting side.
TEST(OperatorAndExpressionParsing, UnparenthesizedAssignInExprIsRejected) {
  auto r = Parse(
      "module t;\n"
      "  int a, b, c;\n"
      "  initial a = b = c;\n"
      "endmodule\n");
  // The second '=' is left standing where the statement terminator belongs, so
  // §12.3 reports it: §11.3.6 has no report of its own for the unparenthesized
  // form.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got '='", 3, "12.3"));
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
