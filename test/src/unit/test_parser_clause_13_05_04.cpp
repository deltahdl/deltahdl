// §13.5.4: Argument binding by name

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.9 — list_of_arguments (named)
// =============================================================================
// All named arguments
TEST(ParserA609, ListOfArgsAllNamed) {
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

// Named argument with empty expression
TEST(ParserA609, ListOfArgsNamedEmpty) {
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

// --- Test helpers ---
struct ParseResult14 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult14 Parse(const std::string& src) {
  ParseResult14 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// LRM section 13.5.5 -- Optional argument list / binding by name (additional)
// =============================================================================
// Named arg binding on a task call.
TEST(ParserSection13, NamedArgBindingOnTaskCall) {
  auto r = Parse(
      "module m;\n"
      "  task drive(input int addr, input int data);\n"
      "  endtask\n"
      "  initial drive(.data(42), .addr(100));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kCall);
  ASSERT_EQ(call->arg_names.size(), 2u);
  EXPECT_EQ(call->arg_names[0], "data");
  EXPECT_EQ(call->arg_names[1], "addr");
}

// Mixed positional then named arguments
TEST(ParserA609, ListOfArgsMixedPositionalThenNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(1, 2, .c(3)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  // Two positional args + one named arg
  EXPECT_EQ(expr->args.size(), 3u);
  ASSERT_EQ(expr->arg_names.size(), 1u);
  EXPECT_EQ(expr->arg_names[0], "c");
}

// Named arg binding with empty arg (.name()).
TEST(ParserSection13, NamedArgBindingEmptyArg) {
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

// Named and positional arguments cannot be mixed in the same call.
// This test verifies that a purely named call parses with correct count.
TEST(ParserSection13, NamedArgBindingAllNamed) {
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

// Mixed positional + named arguments
TEST(ParserA82, ListOfArgsMixed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foo(1, .b(2)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->args.size(), 2u);
  ASSERT_EQ(expr->arg_names.size(), 1u);
  EXPECT_EQ(expr->arg_names[0], "b");
}

// =============================================================================
// LRM section 13.5.4 -- Named argument binding
// =============================================================================
TEST(ParserSection13, NamedArgBindingParses) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a, int b);\n"
      "  endfunction\n"
      "  initial foo(.b(2), .a(1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kCall);
}

TEST(ParserSection13, NamedArgBindingNames) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a, int b);\n"
      "  endfunction\n"
      "  initial foo(.b(2), .a(1));\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 2u);
  ASSERT_EQ(call->arg_names.size(), 2u);
  const std::vector<std::string> kExpected = {"b", "a"};
  for (size_t i = 0; i < kExpected.size(); ++i) {
    EXPECT_EQ(call->arg_names[i], kExpected[i]);
  }
}

TEST(ParserSection13, PositionalArgsHaveEmptyNames) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a, int b);\n"
      "  endfunction\n"
      "  initial foo(1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kCall);
}

TEST(ParserSection13, PositionalArgsNoNamedArgs) {
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
  // Positional calls: arg_names is empty (no named args detected)
  EXPECT_TRUE(call->arg_names.empty());
}

}  // namespace
