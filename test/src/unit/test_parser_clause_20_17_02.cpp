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

// §20.17.2: $stacktrace can be called as a function. On the right-hand side of
// an assignment it parses as the same argument-less system call.
TEST(StacktraceCall, ParsesAsFunctionInAssignment) {
  auto r = Parse("module m; string s; initial s = $stacktrace; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$stacktrace");
  EXPECT_EQ(stmt->rhs->args.size(), 0u);
}

}  // namespace
