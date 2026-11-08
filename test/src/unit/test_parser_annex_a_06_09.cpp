#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

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

TEST(SubroutineCallStatementParsing, TaskCallRequiresSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial foo(1, 2)\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "12.3"));
}

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

TEST(SubroutineCallStatementParsing, VoidCastRequiresSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial void'(compute(3))\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "12.3"));
}

TEST(SubroutineCallStatementParsing, VoidCastOfNonCallIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial void'(a + b);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a void cast discards a function call's return value", 2,
      "A.6.9"));
}

TEST(SubroutineCallStatementParsing, VoidCastInExpressionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = void'(compute(3));\n"
      "    if (void'(compute(3))) y = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a void cast is a statement, void'(function_subroutine_call);",
      3, "A.6.9"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a void cast is a statement, void'(function_subroutine_call);",
      4, "A.6.9"));
}

TEST(SubroutineCallStatementParsing, VoidCastOfEveryCallForm) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    void'(compute(3));\n"
      "    void'(obj.next());\n"
      "    lbl: void'($urandom());\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* block = InitialBody(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->kind, StmtKind::kBlock);
  ASSERT_EQ(block->stmts.size(), 3u);
  for (auto* stmt : block->stmts) {
    EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
    ASSERT_NE(stmt->expr, nullptr);
    EXPECT_EQ(stmt->expr->kind, ExprKind::kCast);
    EXPECT_EQ(stmt->expr->text, "void");
  }
  EXPECT_EQ(block->stmts[1]->expr->lhs->kind, ExprKind::kCall);
  EXPECT_EQ(block->stmts[2]->expr->lhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(block->stmts[2]->label, "lbl");
}

TEST(SubroutineCallStatementParsing, VoidCastOfACallWithAClauseAndNoParens) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    void'(q.find with (item > 1));\n"
      "    void'(q.sum with (item * 2));\n"
      "    void'(obj.randomize with { x > 0; });\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* block = InitialBody(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->stmts.size(), 3u);
  for (auto* stmt : block->stmts) {
    ASSERT_NE(stmt->expr, nullptr);
    EXPECT_EQ(stmt->expr->kind, ExprKind::kCast);
  }
}

TEST(SubroutineCallStatementParsing, ABareNewIsNoStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    new;\n"
      "    new c;\n"
      "    new[4];\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "'new' is no subroutine call", 3, "A.6.9"));
  EXPECT_TRUE(
      ReportedError(r.diags, "'new' is no subroutine call", 4, "A.6.9"));
  EXPECT_TRUE(
      ReportedError(r.diags, "'new' is no subroutine call", 5, "A.6.9"));
}

TEST(SubroutineCallStatementParsing, SuperNewIsAStatement) {
  auto r = Parse(
      "class B; function new(int x); endfunction endclass\n"
      "class D extends B;\n"
      "  function new();\n"
      "    super.new(3);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallStatementParsing, VoidCastOfACallWithoutItsArguments) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    void'(obj.get);\n"
      "    void'(obj.randomize);\n"
      "    void'(get);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* block = InitialBody(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->stmts.size(), 3u);
  EXPECT_EQ(block->stmts[0]->expr->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(block->stmts[2]->expr->lhs->kind, ExprKind::kIdentifier);
}

}  // namespace
