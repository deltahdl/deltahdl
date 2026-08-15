#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "helpers_subroutine_call_verify.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprParsing, NestedFunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  initial x = f(g(1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->callee, "f");
  ASSERT_EQ(stmt->rhs->args.size(), 1u);
  ASSERT_NE(stmt->rhs->args[0], nullptr);
  EXPECT_EQ(stmt->rhs->args[0]->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->args[0]->callee, "g");
}

TEST(SubroutineCallExprParsing, ListOfArgsPositionalOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(1, 2, 3); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->args.size(), 3u);
  EXPECT_TRUE(expr->arg_names.empty());
}

TEST(SubroutineCallExprParsing, ListOfArgsEmptyPlaceholders) {
  // list_of_arguments permits omitted (empty) positional elements; the parser
  // must record a null entry for each so later argument positions stay aligned.
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(1, , 3); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  ASSERT_EQ(expr->args.size(), 3u);
  EXPECT_NE(expr->args[0], nullptr);
  EXPECT_EQ(expr->args[1], nullptr);
  EXPECT_NE(expr->args[2], nullptr);
  EXPECT_TRUE(expr->arg_names.empty());
}

TEST(SubroutineCallExprParsing, ListOfArgsLeadingEmptyPlaceholder) {
  // A leading empty element is also a valid positional placeholder.
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(, 5); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  ASSERT_EQ(expr->args.size(), 2u);
  EXPECT_EQ(expr->args[0], nullptr);
  EXPECT_NE(expr->args[1], nullptr);
}

TEST(SubroutineCallExprParsing, ExprAsFunctionArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(a + b, c * d, {e, f});\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, FunctionCallEmptyArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = fn();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->callee, "fn");
  EXPECT_EQ(stmt->rhs->args.size(), 0u);
}

TEST(SubroutineCallSyntaxParsing, TaskCallAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin my_task(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->callee, "my_task");
  EXPECT_EQ(expr->args.size(), 0u);
}

TEST(SubroutineCallSyntaxParsing, ErrorMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial foo(1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 2, "13.5"));
}

// Syntax 13-3 gives subroutine_call_statement a second alternative,
// void ' ( function_subroutine_call ) ;. The A.8.2 view of the same input,
// which alternative of subroutine_call sits inside the cast, is
// VoidCastFunctionCall in test_parser_annex_a_08_02.cpp.
TEST(SubroutineCallSyntaxParsing, VoidCastSubroutineCallStatement) {
  VerifyVoidCastFunctionCall();
}

TEST(SubroutineCallSyntaxParsing, VoidFunctionCallAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  function void myprint(int a);\n"
      "    $display(\"%d\", a);\n"
      "  endfunction\n"
      "  initial myprint(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kCall);
}

// 13.5 binds arguments by position unless they are named; a method call
// carries such a positional list_of_arguments. The A.8.2 method_call_body
// view is MethodCallWithArgs in test_parser_annex_a_08_02.cpp.
TEST(SubroutineCallSyntaxParsing, MethodCallWithPositionalArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.method(1, 2); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->args.size(), 2u);
}

TEST(SubroutineCallSyntaxParsing, SystemTaskCallAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

// The void ' ( function_subroutine_call ) ; alternative of
// subroutine_call_statement needs both parentheses. The annex counterpart is
// ErrorVoidCastMissingCloseParen in test_parser_annex_a_08_02.cpp.
TEST(SubroutineCallSyntaxParsing, ErrorVoidCastStatementMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo();\n"
      "endmodule\n");
  // §6.24.1 owns the cast parentheses, so the report for the unclosed
  // `void'(` is filed there rather than under §13.5.
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 3, "6.24.1"));
}

// A void-cast subroutine_call_statement still terminates with a semicolon.
// The annex counterpart is ErrorVoidCastMissingSemicolon in
// test_parser_annex_a_08_02.cpp.
TEST(SubroutineCallSyntaxParsing, ErrorVoidCastStatementMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial begin\n"
      "    void'(foo())\n"
      "  end\n"
      "endmodule\n");
  // §12.3 owns the semicolon that ends a statement, and the `end` on line 5 is
  // the token standing where it belongs. Parser::Expect names every keyword
  // "token".
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got token", 5, "12.3"));
}

}  // namespace
