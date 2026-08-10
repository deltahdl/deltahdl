#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SubroutineCallSyntaxParsing, ListOfArgsAllNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(.a(1), .b(2)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->arg_names.size(), 2u);
  EXPECT_EQ(expr->arg_names[0], "a");
  EXPECT_EQ(expr->arg_names[1], "b");
  EXPECT_EQ(expr->args.size(), 2u);
}

TEST(SubroutineCallSyntaxParsing, ListOfArgsNamedEmpty) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(.a(), .b(1)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->arg_names.size(), 2u);
  EXPECT_EQ(expr->args[0], nullptr);
  ASSERT_NE(expr->args[1], nullptr);
}

TEST(SubroutineCallSyntaxParsing, ListOfArgsMixedPositionalThenNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(1, 2, .c(3)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);

  EXPECT_EQ(expr->args.size(), 3u);
  ASSERT_EQ(expr->arg_names.size(), 1u);
  EXPECT_EQ(expr->arg_names[0], "c");
}

TEST(TaskAndFunctionParsing, NamedArgBindingEmptyArg) {
  auto r = Parse(
      "module m;\n"
      "  function int fun(int j = 1, string s = \"no\");\n"
      "    return j;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = fun(.s(), .j());\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  ASSERT_EQ(stmt->rhs->arg_names.size(), 2u);
  EXPECT_EQ(stmt->rhs->arg_names[0], "s");
  EXPECT_EQ(stmt->rhs->arg_names[1], "j");
}

TEST(TaskAndFunctionParsing, NamedArgBindingAllNamed) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b, int c);\n"
      "    return a + b + c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = add(.c(3), .a(1), .b(2));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  ASSERT_EQ(stmt->rhs->arg_names.size(), 3u);
  EXPECT_EQ(stmt->rhs->arg_names[0], "c");
  EXPECT_EQ(stmt->rhs->arg_names[1], "a");
  EXPECT_EQ(stmt->rhs->arg_names[2], "b");
}

TEST(TaskAndFunctionParsing, PositionalArgsNoNamedArgs) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a, int b);\n"
      "  endfunction\n"
      "  initial foo(1, 2);\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 2u);

  EXPECT_TRUE(call->arg_names.empty());
}

TEST(TaskAndFunctionParsing, PositionalAfterNamedIsError) {
  auto r = Parse(
      "module m;\n"
      "  function int fun(int j = 1, string s = \"no\");\n"
      "    return j;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = fun(.s(\"yes\"), 2);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §13.5.4 writes an argument bound by name as `. identifier ( expression )`. An
// argument whose parentheses are left open is rejected at the token standing
// where the ')' belongs, and the report names §13.5.4 rather than the token it
// wanted. The call's own report follows it, because the argument is the
// innermost construct the source ran out of.
TEST(NamedArgument, MalformedNamedArgumentNames13_5_4) {
  auto r = Parse(
      "module m;\n"
      "  initial f(.a(1);\n"
      "endmodule\n");
  ASSERT_FALSE(r.diags.empty());
  EXPECT_EQ(r.diags.front().subclause, "13.5.4");
  EXPECT_EQ(r.diags.front().loc.line, 2u);
  EXPECT_EQ(r.diags.front().loc.column, 17u);
}

}  // namespace
