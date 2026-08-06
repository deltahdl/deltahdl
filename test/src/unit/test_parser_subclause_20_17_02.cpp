#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Syntax 20-18: stacktrace_call ::= $stacktrace. The production carries no
// argument list, so a bare $stacktrace used as a statement parses as a system
// call whose callee is $stacktrace and that has no arguments.
TEST(StacktraceCall, ParsesAsArgumentlessTask) {
  auto r = Parse("module m; initial $stacktrace; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$stacktrace");
  EXPECT_EQ(stmt->expr->args.size(), 0u);
}

// Syntax 20-18: the same argumentless production also stands in expression
// position — the function form. On the right-hand side of a blocking
// assignment, bare $stacktrace (no parentheses, no arguments) parses as a
// system-call operand.
TEST(StacktraceCall, ParsesAsArgumentlessExpressionOperand) {
  auto r =
      Parse("module m; string trace; initial trace = $stacktrace; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$stacktrace");
  EXPECT_EQ(stmt->rhs->args.size(), 0u);
}

}  // namespace
