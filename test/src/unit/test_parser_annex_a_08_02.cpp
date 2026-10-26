#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "helpers_subroutine_call_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprParsing, FunctionCallExpr) {
  auto r = Parse("module m; initial x = func(a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(SubroutineCallExprParsing, SystemTfCallMultipleExprArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"%d %d\", 1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->args.size(), 3u);
}

TEST(SubroutineCallExprParsing, SystemTfCallEmptyArgSlots) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(,,42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->args.size(), 3u);
  EXPECT_EQ(expr->args[0], nullptr);
  EXPECT_EQ(expr->args[1], nullptr);
  ASSERT_NE(expr->args[2], nullptr);
}

TEST(SubroutineCallExprParsing, ListOfArgsNamedEmptyExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(.a(), .b(1)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->arg_names.size(), 2u);
  EXPECT_EQ(expr->args[0], nullptr);
  ASSERT_NE(expr->args[1], nullptr);
}

TEST(SubroutineCallSyntaxParsing, CallWithSingleArg) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(42); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->args.size(), 1u);
}

TEST(SubroutineCallSyntaxParsing, MethodCallChained) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a.b.c(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

// tf_call permits the parenthesized list_of_arguments to be omitted entirely,
// the counterpart of SystemCallWithoutParens for a user-defined task. The
// prose rule that licenses the omission is covered by TaskCallWithoutParens in
// test_parser_subclause_13_05_05.cpp.
TEST(SubroutineCallSyntaxParsing, TfCallWithoutParens) {
  auto r = Parse(
      "module m;\n"
      "  task foo; endtask\n"
      "  initial foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(SubroutineCallSyntaxParsing, VoidCastFunctionCall) {
  VerifyVoidCastFunctionCall();
}

TEST(SubroutineCallSyntaxParsing, MethodCallWithArgs) {
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

TEST(SubroutineCallSyntaxParsing, VoidCastSystemCall) {
  auto r = Parse(
      "module m;\n"
      "  initial void'($sformatf(\"hello\"));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCast);
  EXPECT_EQ(expr->text, "void");
  ASSERT_NE(expr->lhs, nullptr);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kSystemCall);
}

// A tf_call naming a user-defined void function stands alone as a statement.
// The 13.5 prose form of the same claim is VoidFunctionCallAsStatement in
// test_parser_subclause_13_05.cpp.
TEST(SubroutineCallSyntaxParsing, VoidFunctionTfCallAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  function void myprint(int a);\n"
      "    $display(\"%d\", a);\n"
      "  endfunction\n"
      "  initial myprint(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kCall);
}

TEST(SubroutineCallSyntaxParsing, CallWithEmptyParens) {
  auto r = Parse(
      "module m;\n"
      "  task foo; endtask\n"
      "  initial foo();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->callee, "foo");
  EXPECT_TRUE(expr->args.empty());
}

TEST(SubroutineCallSyntaxParsing, SubroutineCallAsStatement) {
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
}

TEST(SubroutineCallSyntaxParsing, CallWithMultipleArgs) {
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
}

TEST(SubroutineCallSyntaxParsing, SystemCallWithoutParens) {
  auto r = Parse(
      "module m;\n"
      "  initial $finish;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->callee, "$finish");
  EXPECT_TRUE(expr->args.empty());
}

TEST(SubroutineCallSyntaxParsing, MethodCallNoArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  ASSERT_NE(expr->lhs, nullptr);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kMemberAccess);
}

TEST(SubroutineCallSyntaxParsing, ThisMethodCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin this.method(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(SubroutineCallSyntaxParsing, VoidCastOfMethodCall) {
  auto r = Parse(
      "module m;\n"
      "  initial void'(obj.method());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCast);
  EXPECT_EQ(expr->text, "void");
  ASSERT_NE(expr->lhs, nullptr);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kCall);
}

TEST(SubroutineCallSyntaxParsing, ErrorCallMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foo()\n"
      "  end\n"
      "endmodule\n");
  // §12.3 owns the semicolon that ends a statement; the report stands at the
  // 'end' that arrived instead.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'end'", 4, "12.3"));
}

TEST(SubroutineCallSyntaxParsing, ErrorVoidCastMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial begin\n"
      "    void'(foo())\n"
      "  end\n"
      "endmodule\n");
  // §12.3 owns the semicolon that ends a statement; the report stands at the
  // 'end' that arrived instead.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'end'", 5, "12.3"));
}

TEST(SubroutineCallSyntaxParsing, ErrorVoidCastMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'foo());\n"
      "endmodule\n");
  // The parser never reaches the cast: an apostrophe not followed by '(' or a
  // base is no token of §5.6, so Lexer::LexOperator in
  // src/lexer/lexer_operators.cpp rejects the character itself. §6.24.1 owns
  // the cast operator's parentheses and has no report of its own here.
  EXPECT_TRUE(ReportedError(r.diags, "unexpected character '''", 3, "5.2"));
}

TEST(SubroutineCallSyntaxParsing, ErrorVoidCastMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo();\n"
      "endmodule\n");
  // A.6.9 writes the void cast statement's parentheses, `void ' (
  // function_subroutine_call ) ;`, and Parser::ParseVoidCastCallStmt reads
  // them: A.8.4's casting_type names no `void`, so §6.24.1's cast operator is
  // not what stands here.
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 3, "A.6.9"));
}

TEST(SubroutineCallExprParsing, ListOfArgsAllNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(.a(1), .b(2), .c(3)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->arg_names.size(), 3u);
  EXPECT_EQ(expr->args.size(), 3u);
}

TEST(SubroutineCallExprParsing, ListOfArgsMixedPositionalAndNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(1, 2, .c(3)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(SubroutineCallExprParsing, ArrayMethodNameUnique) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = q.unique;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, RandomizeCallBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, RandomizeCallWithConstraintBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    obj.randomize() with { x < 10; };\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// A.8.2 makes a method_call's root a primary, and A.8.4 counts a parenthesized
// mintypmax_expression among the primaries, so a method is called on the
// handle a parenthesized expression yields (§8.4): the call's receiver is the
// conditional expression inside the parentheses.
TEST(SubroutineCallExprParsing, MethodCallOnAParenthesizedExpression) {
  auto r = Parse(
      "class D;\n"
      "  function int f(); return 1; endfunction\n"
      "endclass\n"
      "module m(input logic sel);\n"
      "  D x = new;\n"
      "  D y = new;\n"
      "  int i;\n"
      "  initial i = (sel ? x : y).f();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  ASSERT_EQ(stmt->rhs->lhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(stmt->rhs->lhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->lhs->kind, ExprKind::kTernary);
  ASSERT_NE(stmt->rhs->lhs->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->rhs->text, "f");
}

// A randomize_call (A.8.2) is a built_in_method_call, so it too takes a
// parenthesized receiver, with its inline constraint block after it.
TEST(SubroutineCallExprParsing, RandomizeWithOnAParenthesizedExpression) {
  auto r = Parse(
      "class D;\n"
      "  rand int v;\n"
      "endclass\n"
      "module m(input logic sel);\n"
      "  D x = new;\n"
      "  D y = new;\n"
      "  int ok;\n"
      "  initial ok = (sel ? x : y).randomize() with { v < 10; };\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  EXPECT_NE(stmt->rhs->inline_constraint, nullptr);
}

TEST(SubroutineCallExprParsing, SuperMethodCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin super.method(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, SystemTfCallDataTypeArg) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial x = $bits(logic [7:0]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, ErrorSystemCallMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hi\";\n"
      "endmodule\n");
  // §13.5 owns the argument-list parentheses of a subroutine call.
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 2, "13.5"));
}

TEST(SubroutineCallExprParsing, FunctionCallInBinaryExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial x = f(1) + g(2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  ASSERT_NE(stmt->rhs->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->rhs->kind, ExprKind::kCall);
}

TEST(SubroutineCallExprParsing, ArrayMethodNameAnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.and;\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, ArrayMethodNameOr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.or;\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, ArrayMethodNameXor) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.xor;\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, ArrayManipulationCallWithExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.sum() with (item > 0);\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, RandomizeWithNullArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin obj.randomize(null); end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, RandomizeWithVariableIdentifierList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin obj.randomize(a, b, c); end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, RandomizeWithIdentifierListInParensAndBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin obj.randomize() with (a, b) { a < b; }; end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, RandomizeWithEmptyParensAndBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin obj.randomize() with () { x > 0; }; end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, ScopeRandomizeWithStdPrefix) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int a, b;\n"
              "  initial begin std::randomize(a, b); end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, SystemTfCallWithClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk;\n"
              "  int a;\n"
              "  initial $display(a, @clk);\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, ConstantFunctionCallInParameter) {
  auto r = Parse(
      "module m;\n"
      "  function int f(int a); return a + 1; endfunction\n"
      "  parameter P = f(3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, TfCallPackageScopedIdentifier) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin pkg::do_it(); end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, TfCallWithAttributeInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin foo (* annotated *) (1); end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, MethodCallBodyWithAttributeInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin obj.method (* annotated *) (1); end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, ArrayManipulationCallWithArgList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.sum(1);\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, ArrayManipulationCallWithAttributeInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.unique (* annotated *) ();\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, RandomizeCallWithAttributeInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin obj.randomize (* annotated *) (); end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, RandomizeCallSingleVariableIdentifier) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin obj.randomize(a); end\n"
              "endmodule\n"));
}

TEST(SubroutineCallExprParsing, SystemTfCallDataTypeAndExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int x;\n"
              "  initial x = $bits(logic [7:0], 1);\n"
              "endmodule\n"));
}

// A.8.2 with A.8.3: an assignment in its own parentheses is no primary, so a
// method call or member select applied to it is reported (#7725).
TEST(SubroutineCallExprParsing, AMethodOfAnAssignmentInItsOwnParensIsReported) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (h = g).run();\n"
      "    x = (h = g).n;\n"
      "  end\n"
      "endmodule\n");
  constexpr const char* kMessage =
      "a method call or member select applies to a primary, and an "
      "assignment in its own parentheses is none; enclose it in a second "
      "pair of parentheses";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 3, "A.8.2"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 4, "A.8.2"));
}

// A.8.4: an assignment in a second pair of parentheses is a primary a method
// is called on, and one in its own parentheses is an operand (§11.3.6).
TEST(SubroutineCallExprParsing, AnAssignmentInASecondPairOfParensTakesAMethod) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ((h = g)).run();\n"
      "    x = (y = 1) + 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// A.8.2's list_of_arguments holds no `default`: A.1.9 writes the keyword in
// place of an argument list only in a constructor's super.new call (§8.17),
// so it is reported in any other call and in a class new (#8055).
TEST(SubroutineCallExprParsing, ADefaultArgumentListIsReportedOutsideSuperNew) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = f(default);\n"
      "    obj.m(default);\n"
      "    h = new(default);\n"
      "    super.f(default);\n"
      "  end\n"
      "endmodule\n");
  constexpr const char* kMessage =
      "'default' stands in place of an argument list only in a constructor's "
      "super.new call";
  for (uint32_t line = 3; line <= 6; ++line) {
    EXPECT_TRUE(ReportedError(r.diags, kMessage, line, "A.8.2"));
  }
}

TEST(SubroutineCallExprParsing, SuperNewTakesADefaultArgumentList) {
  EXPECT_TRUE(
      ParseOk("class B;\n"
              "  function new(int a); endfunction\n"
              "endclass\n"
              "class D extends B;\n"
              "  function new(default);\n"
              "    super.new(default);\n"
              "  endfunction\n"
              "endclass\n"));
}

// A.8.2 writes an argument list after the name of a subroutine or a method,
// so none follows a call or a select (#8056).
TEST(SubroutineCallExprParsing, AnArgumentListAfterACallOrASelectIsReported) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = f(1)(2);\n"
      "    x = a[0](1);\n"
      "  end\n"
      "endmodule\n");
  constexpr const char* kMessage =
      "an argument list follows the name of a subroutine or a method, not a "
      "call or a select";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 3, "A.8.2"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 4, "A.8.2"));
}

// A.8.4 lets a select follow a call, and a member or a method follow either.
TEST(SubroutineCallExprParsing, ASelectOrAMethodFollowsACall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = f(1)[0];\n"
              "    x = a[0].f(1);\n"
              "    x = f(1).g();\n"
              "  end\n"
              "endmodule\n"));
}

// A.8.2 writes a with clause in an array_manipulation_call, after a method
// named through `.`, and in a randomize_call, written bare, under std:: or as
// a method; after anything else it is reported (#8057).
TEST(SubroutineCallExprParsing, AWithClauseAfterNoArrayMethodOrRandomize) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = y with (z);\n"
      "    x = f(1) with (z);\n"
      "    x = a[0] with (z);\n"
      "    x = pkg::randomize(v) with { v > 0; };\n"
      "    x = pkg::q with (z);\n"
      "  end\n"
      "endmodule\n");
  constexpr const char* kMessage =
      "a with clause follows only an array method call or a randomize call";
  for (uint32_t line = 3; line <= 7; ++line) {
    EXPECT_TRUE(ReportedError(r.diags, kMessage, line, "A.8.2"));
  }
}

TEST(SubroutineCallExprParsing, AnArrayMethodOrARandomizeCallTakesAWithClause) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = q.find with (item > 0);\n"
              "    x = q.sum() with (item);\n"
              "    x = randomize(v) with { v > 0; };\n"
              "    x = std::randomize(v) with { v > 0; };\n"
              "    x = obj.randomize with { v > 0; };\n"
              "  end\n"
              "endmodule\n"));
}

// A.8.2 (printed page 1209): a randomize_call's argument list is optional,
// so a randomize name followed by a with clause, under std::, after a `.` or
// bare, and std::randomize alone, are each the call randomize() is, the
// constraint block on that call. A member named randomize with neither,
// which may be a struct's, stays the member it reads as (#8151).
TEST(SubroutineCallExprParsing, ARandomizeCallWithoutItsListIsACall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = std::randomize with { a > 0; };\n"
      "    x = obj.randomize with { v > 0; };\n"
      "    x = randomize with { v > 0; };\n"
      "    x = std::randomize;\n"
      "    x = s.randomize;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const std::vector<Stmt*> kStmts = AllInitialStmts(r);
  ASSERT_EQ(kStmts.size(), 5u);
  for (size_t i = 0; i < 3; ++i) {
    const Expr* rhs = kStmts[i]->rhs;
    ASSERT_EQ(rhs->kind, ExprKind::kCall) << "statement " << i;
    EXPECT_TRUE(rhs->args.empty()) << "statement " << i;
    EXPECT_NE(rhs->inline_constraint, nullptr) << "statement " << i;
  }
  EXPECT_EQ(kStmts[3]->rhs->kind, ExprKind::kCall);
  EXPECT_EQ(kStmts[3]->rhs->inline_constraint, nullptr);
  EXPECT_EQ(kStmts[4]->rhs->kind, ExprKind::kMemberAccess);
}

// A.8.2's randomize_call writes after `with` an optional parenthesized list
// of identifiers and then a constraint block, which is required (#8058).
TEST(SubroutineCallExprParsing, ARandomizeWithClauseNamesAndEndsInABlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = obj.randomize() with (a);\n"
      "    x = obj.randomize() with (a + 1, b) { a > 0; };\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a randomize call's with clause ends in a constraint block", 3,
      "A.8.2"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "a randomize call's with clause lists identifiers "
                            "alone in its parentheses",
                            4, "A.8.2"));
}

// A.8.2's array_manipulation_call writes after `with` one expression in
// parentheses and no constraint block (#8059).
TEST(SubroutineCallExprParsing, AnArrayMethodsWithClauseHoldsOneExpression) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    x = q.sum with { item > 0; };\n"
      "    x = q.sum with (item) { item > 0; };\n"
      "    x = q.sum with ();\n"
      "    x = q.sum with (item, item + 1);\n"
      "  end\n"
      "endmodule\n");
  constexpr const char* kBlock =
      "an array method's with clause takes no constraint block";
  constexpr const char* kOne =
      "an array method's with clause holds one expression in its parentheses";
  EXPECT_TRUE(ReportedError(r.diags, kBlock, 4, "A.8.2"));
  EXPECT_TRUE(ReportedError(r.diags, kBlock, 5, "A.8.2"));
  EXPECT_TRUE(ReportedError(r.diags, kOne, 6, "A.8.2"));
  EXPECT_TRUE(ReportedError(r.diags, kOne, 7, "A.8.2"));
}

// A.8.2's randomize_call takes variable identifiers or `null` alone, so no
// `null` beside a name, no empty position and no named argument (#8060).
TEST(SubroutineCallExprParsing, ARandomizeArgumentListIsNamesOrNullAlone) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = obj.randomize(a, null);\n"
      "    x = obj.randomize(a, , b);\n"
      "    x = obj.randomize(.a(b));\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'null' stands alone in a randomize call's argument list", 3,
      "A.8.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a randomize call's argument list leaves no position empty", 4,
      "A.8.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a randomize call passes no argument by name", 5, "A.8.2"));
}

// A.8.2's system_tf_call takes a data_type as its first argument, and A.2.2.1
// gives a data_type a signing, the struct, union and enum types, a virtual
// interface, chandle and event, none of which an expression spells: each is
// read whole into a kTypeRef node carrying the type (#8061).
TEST(SubroutineCallExprParsing, ASystemCallTakesATypeNoExpressionSpells) {
  const std::pair<const char*, DataTypeKind> kTypes[] = {
      {"int unsigned", DataTypeKind::kInt},
      {"bit signed [3:0]", DataTypeKind::kBit},
      {"struct packed { bit a; byte b; }", DataTypeKind::kStruct},
      {"union packed { byte a; byte b; }", DataTypeKind::kUnion},
      {"enum {A, B}", DataTypeKind::kEnum},
      {"virtual ifc", DataTypeKind::kVirtualInterface},
      {"chandle", DataTypeKind::kChandle},
      {"event", DataTypeKind::kEvent},
  };
  for (const auto& [type, kind] : kTypes) {
    auto r = Parse(std::string("module m;\n  initial s = $typename(") + type +
                   ");\nendmodule\n");
    EXPECT_FALSE(r.has_errors) << type;
    const Expr* call = FirstInitialRHS(r);
    ASSERT_NE(call, nullptr) << type;
    ASSERT_EQ(call->args.size(), 1u) << type;
    ASSERT_EQ(call->args[0]->kind, ExprKind::kTypeRef) << type;
    ASSERT_NE(call->args[0]->type_value, nullptr) << type;
    EXPECT_EQ(call->args[0]->type_value->kind, kind) << type;
  }
}

// A.8.2 writes a system call's clocking event after a first expression, so
// none follows an empty first position (#8062).
TEST(SubroutineCallExprParsing, AClockingEventAfterAnEmptyFirstArgument) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  initial x = $rose(, @(posedge clk));\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a clocking event follows a system call's "
                            "arguments only after a first expression",
                            3, "A.8.2"));
}

TEST(SubroutineCallExprParsing, AClockingEventAfterAFirstExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk, a;\n"
              "  initial begin\n"
              "    x = $rose(a, @(posedge clk));\n"
              "    x = $past(a, 1, , @(posedge clk));\n"
              "  end\n"
              "endmodule\n"));
}

// A.8.2 makes any primary a method call's root, and A.8.4 counts among the
// primaries a literal, an assignment pattern expression with or without its
// type, the empty unpacked array concatenation, a streaming concatenation,
// null, $, and a cast whose type is a size or a type reference (#8063).
TEST(SubroutineCallExprParsing, EveryPrimaryTakesAMethodCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int arr_t [3];\n"
              "  initial begin\n"
              "    n = arr_t'{1, 2, 3}.sum();\n"
              "    n = u_t'{1, 2}.sum();\n"
              "    n = int'{1, 2}.sum();\n"
              "    n = '{1, 2}.sum();\n"
              "    n = type(arr_t)'{1, 2, 3}.sum();\n"
              "    n = type(arr_t)'(q).sum();\n"
              "    n = 8'(x).f();\n"
              "    n = \"abc\".len();\n"
              "    n = null.f();\n"
              "    n = $.f();\n"
              "    n = {}.size();\n"
              "    n = {>>{a}}.size();\n"
              "  end\n"
              "endmodule\n"));
}

// A.8.2's method_call_body writes attribute instances between a method's name
// and its arguments, whatever primary the method is called on (#8064).
TEST(SubroutineCallExprParsing, AMethodOnAnyPrimaryTakesAttributeInstances) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial begin\n"
              "    n = string'(s).len (* a *) ();\n"
              "    n = (h).f (* a *) (1);\n"
              "    n = $sformatf(\"%d\", n).len (* a *) ();\n"
              "    n = q.find with (item > 0).size (* a *) ();\n"
              "  end\n"
              "endmodule\n"));
}

// A.8.2 lets an array method end in a with clause whatever primary it is
// called on: the queue another with clause's call returns, a cast, or a
// $unit:: name (#8065).
TEST(SubroutineCallExprParsing, AnArrayMethodOnAnyPrimaryTakesAWithClause) {
  EXPECT_TRUE(
      ParseOk("typedef int q_t [$];\n"
              "q_t q;\n"
              "module m;\n"
              "  q_t r;\n"
              "  initial begin\n"
              "    r = q.find with (item > 0).find with (item < 9);\n"
              "    r = q_t'(r).find with (item > 0);\n"
              "    r = $unit::q.find with (item > 0);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
