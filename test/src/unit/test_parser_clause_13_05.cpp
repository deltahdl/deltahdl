#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial foo(1;\n"
              "endmodule\n"));
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

TEST(SubroutineCallSyntaxParsing, ErrorVoidCastMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  function int foo(); return 1; endfunction\n"
              "  initial void'(foo();\n"
              "endmodule\n"));
}

TEST(SubroutineCallSyntaxParsing, ErrorVoidCastMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  function int foo(); return 1; endfunction\n"
              "  initial begin\n"
              "    void'(foo())\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
