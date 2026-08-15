#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Annex A.6.9 defines a single grammar production:
//
//   subroutine_call_statement ::=
//       subroutine_call ;
//     | void ' ( function_subroutine_call ) ;
//
// The component productions subroutine_call and function_subroutine_call are
// owned by A.8.2 (already satisfied). These tests observe the statement form
// itself: that the parser's statement dispatch accepts a bare subroutine call,
// or a void cast of a function call, as a complete procedural statement, and
// that the terminating semicolon is required.

// --- Alternative 1: subroutine_call ; ---

TEST(SubroutineCallStatementParsing, TaskCallAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial foo(1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kCall);
}

TEST(SubroutineCallStatementParsing, SystemTaskCallAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hi\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

// The terminating semicolon belongs to the subroutine_call_statement
// production; without it the statement is rejected.
TEST(SubroutineCallStatementParsing, TaskCallRequiresSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial foo(1, 2)\n"
      "endmodule\n");
  // §12.3 owns the semicolon that closes an expression statement; A.6.9 states
  // the production but has no report of its own.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got token", 3, "12.3"));
}

// --- Alternative 2: void ' ( function_subroutine_call ) ; ---

TEST(SubroutineCallStatementParsing, VoidCastOfFunctionCallAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial void'(compute(3));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kCast);
  EXPECT_EQ(stmt->expr->text, "void");
  ASSERT_NE(stmt->expr->lhs, nullptr);
  EXPECT_EQ(stmt->expr->lhs->kind, ExprKind::kCall);
}

// The semicolon is equally required for the void-cast form.
TEST(SubroutineCallStatementParsing, VoidCastRequiresSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial void'(compute(3))\n"
      "endmodule\n");
  // §12.3 owns the semicolon that closes an expression statement; the void cast
  // reaches the same statement form as a bare subroutine call.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got token", 3, "12.3"));
}

}  // namespace
