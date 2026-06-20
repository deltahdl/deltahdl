#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprParsing, SystemFunctionCall) {
  auto r = Parse(
      "module m; initial begin $display(\"v=%0d\", x); $finish; end "
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(SubroutineCallSyntaxParsing, TaskCallWithoutParens) {
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
  auto r = Parse(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCast);
  EXPECT_EQ(expr->text, "void");
  ASSERT_NE(expr->lhs, nullptr);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kCall);
  EXPECT_EQ(expr->lhs->callee, "foo");
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

TEST(SubroutineCallSyntaxParsing, TaskCalledAsStatement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task greet; endtask\n"
              "  initial greet();\n"
              "endmodule\n"));
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

TEST(SubroutineCallSyntaxParsing, VoidFunctionCallAsStatement) {
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

TEST(SubroutineCallSyntaxParsing, VoidCastOfChainedMethodCall) {
  auto r = Parse(
      "module m;\n"
      "  initial void'(a.b.c());\n"
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
  EXPECT_TRUE(r.has_errors);
}

TEST(SubroutineCallSyntaxParsing, ErrorVoidCastMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial begin\n"
      "    void'(foo())\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SubroutineCallSyntaxParsing, ErrorVoidCastMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'foo());\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SubroutineCallSyntaxParsing, ErrorVoidCastMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
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

}  // namespace
