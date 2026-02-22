// Tests for A.8.2 — Subroutine calls — Parser

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Expr *FirstInitialExpr(ParseResult &r) {
  auto *stmt = FirstInitialStmt(r);
  return stmt ? stmt->expr : nullptr;
}

static Expr *FirstContAssignRHS(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign)
      return item->assign_rhs;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.8.2 Subroutine calls — constant_function_call
// =============================================================================

// § constant_function_call ::= function_subroutine_call (footnote 41)

TEST(ParserA82, ConstantFunctionCallInParam) {
  auto r = Parse("module m #(parameter int P = calc(4));\n"
                 "  function int calc(int n); return n * 2; endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  ASSERT_NE(params[0].second, nullptr);
  EXPECT_EQ(params[0].second->kind, ExprKind::kCall);
  EXPECT_EQ(params[0].second->callee, "calc");
}

TEST(ParserA82, ConstantFunctionCallInLocalparam) {
  auto r =
      Parse("module m;\n"
            "  function int clog2_fn(int n); return $clog2(n); endfunction\n"
            "  localparam int W = clog2_fn(256);\n"
            "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.2 Subroutine calls — tf_call
// =============================================================================

// § tf_call ::= ps_or_hierarchical_tf_identifier { attribute_instance }
//              [ ( list_of_arguments ) ]

// tf_call as expression (function return value used in RHS)
TEST(ParserA82, TfCallAsExprInAssign) {
  auto r = Parse("module m;\n"
                 "  initial x = func(1, 2);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->callee, "func");
  EXPECT_EQ(stmt->rhs->args.size(), 2u);
}

// tf_call with no arguments (footnote 42: only legal for tasks/void/class)
TEST(ParserA82, TfCallNoArgs) {
  auto r = Parse("module m;\n"
                 "  initial begin foo(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->callee, "foo");
  EXPECT_TRUE(expr->args.empty());
}

// tf_call in continuous assignment (function_subroutine_call as primary)
TEST(ParserA82, TfCallInContAssign) {
  auto r = Parse("module m;\n"
                 "  wire [7:0] y;\n"
                 "  function logic [7:0] compute(input logic [7:0] a);\n"
                 "    return a + 8'd1;\n"
                 "  endfunction\n"
                 "  assign y = compute(8'd5);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstContAssignRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->callee, "compute");
}

// =============================================================================
// A.8.2 Subroutine calls — system_tf_call
// =============================================================================

// § system_tf_call ::= system_tf_identifier [ ( list_of_arguments ) ]
//   | system_tf_identifier ( data_type [ , expression ] )
//   | system_tf_identifier ( expression { , [ expression ] } ... )

// system_tf_call as expression ($clog2 returns a value)
TEST(ParserA82, SystemTfCallAsExpr) {
  auto r = Parse("module m;\n"
                 "  initial x = $clog2(256);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$clog2");
  EXPECT_EQ(stmt->rhs->args.size(), 1u);
}

// system_tf_call with expression argument: $bits(variable)
TEST(ParserA82, SystemTfCallBitsExprArg) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] v;\n"
                 "  initial x = $bits(v);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$bits");
}

// system_tf_call with multiple expression arguments
TEST(ParserA82, SystemTfCallMultipleExprArgs) {
  auto r = Parse("module m;\n"
                 "  initial $display(\"%d %d\", 1, 2);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->args.size(), 3u);
}

// system_tf_call with empty positional arg slots
TEST(ParserA82, SystemTfCallEmptyArgSlots) {
  auto r = Parse("module m;\n"
                 "  initial $display(,,42);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->args.size(), 3u);
  EXPECT_EQ(expr->args[0], nullptr);
  EXPECT_EQ(expr->args[1], nullptr);
  ASSERT_NE(expr->args[2], nullptr);
}

// =============================================================================
// A.8.2 Subroutine calls — subroutine_call / function_subroutine_call
// =============================================================================

// § subroutine_call ::= tf_call | system_tf_call | method_call
//                      | [ std :: ] randomize_call
// § function_subroutine_call ::= subroutine_call

// function_subroutine_call nested in expression
TEST(ParserA82, FunctionSubroutineCallNested) {
  auto r = Parse("module m;\n"
                 "  initial x = f(g(1));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->callee, "f");
  ASSERT_EQ(stmt->rhs->args.size(), 1u);
  ASSERT_NE(stmt->rhs->args[0], nullptr);
  EXPECT_EQ(stmt->rhs->args[0]->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->args[0]->callee, "g");
}

// function_subroutine_call in binary expression
TEST(ParserA82, FunctionCallInBinaryExpr) {
  auto r = Parse("module m;\n"
                 "  initial x = f(1) + g(2);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  ASSERT_NE(stmt->rhs->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->rhs->kind, ExprKind::kCall);
}

// =============================================================================
// A.8.2 Subroutine calls — list_of_arguments
// =============================================================================

// § list_of_arguments ::=
//   [ expression ] { , [ expression ] } { , . identifier ( [ expression ] ) }
//   | . identifier ( [ expression ] ) { , . identifier ( [ expression ] ) }

// Positional arguments only
TEST(ParserA82, ListOfArgsPositionalOnly) {
  auto r = Parse("module m;\n"
                 "  initial begin foo(1, 2, 3); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->args.size(), 3u);
  EXPECT_TRUE(expr->arg_names.empty());
}

// All named arguments
TEST(ParserA82, ListOfArgsAllNamed) {
  auto r = Parse("module m;\n"
                 "  initial begin foo(.x(10), .y(20)); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->arg_names.size(), 2u);
  EXPECT_EQ(expr->arg_names[0], "x");
  EXPECT_EQ(expr->arg_names[1], "y");
}

// Mixed positional + named arguments
TEST(ParserA82, ListOfArgsMixed) {
  auto r = Parse("module m;\n"
                 "  initial begin foo(1, .b(2)); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->args.size(), 2u);
  ASSERT_EQ(expr->arg_names.size(), 1u);
  EXPECT_EQ(expr->arg_names[0], "b");
}

// Named argument with empty expression
TEST(ParserA82, ListOfArgsNamedEmptyExpr) {
  auto r = Parse("module m;\n"
                 "  initial begin foo(.a(), .b(1)); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->arg_names.size(), 2u);
  EXPECT_EQ(expr->args[0], nullptr);
  ASSERT_NE(expr->args[1], nullptr);
}

// =============================================================================
// A.8.2 Subroutine calls — method_call
// =============================================================================

// § method_call ::= method_call_root . method_call_body
// § method_call_root ::= primary | implicit_class_handle

// Basic method call on identifier
TEST(ParserA82, MethodCallBasic) {
  auto r = Parse("module m;\n"
                 "  initial begin obj.method(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  ASSERT_NE(expr->lhs, nullptr);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kMemberAccess);
}

// Method call with arguments
TEST(ParserA82, MethodCallWithArgs) {
  auto r = Parse("module m;\n"
                 "  initial begin obj.method(1, 2); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  EXPECT_EQ(expr->args.size(), 2u);
}

// Chained method call: a.b.c()
TEST(ParserA82, MethodCallChained) {
  auto r = Parse("module m;\n"
                 "  initial begin a.b.c(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

// method_call_root: implicit_class_handle (this)
TEST(ParserA82, MethodCallRootThis) {
  auto r = Parse("module m;\n"
                 "  initial begin this.method(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

// method_call_root: implicit_class_handle (super)
TEST(ParserA82, MethodCallRootSuper) {
  auto r = Parse("module m;\n"
                 "  initial begin super.method(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

// =============================================================================
// A.8.2 Subroutine calls — method_call_body / built_in_method_call
// =============================================================================

// § method_call_body ::= method_identifier { attribute_instance }
//                        [ ( list_of_arguments ) ]
//                      | built_in_method_call
// § built_in_method_call ::= array_manipulation_call | randomize_call

// =============================================================================
// A.8.2 Subroutine calls — array_manipulation_call
// =============================================================================

// § array_manipulation_call ::= array_method_name { attribute_instance }
//                              [ ( list_of_arguments ) ]
//                              [ with ( expression ) ]

// array_manipulation_call: sum with no args
TEST(ParserA82, ArrayManipCallSum) {
  auto r = Parse("module m;\n"
                 "  initial begin x = arr.sum(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// array_manipulation_call with 'with' clause
TEST(ParserA82, ArrayManipCallWithClause) {
  auto r = Parse("module m;\n"
                 "  int arr[4];\n"
                 "  int result[$];\n"
                 "  initial begin result = arr.find with (item > 5); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.2 Subroutine calls — array_method_name
// =============================================================================

// § array_method_name ::= method_identifier | unique | and | or | xor

TEST(ParserA82, ArrayMethodNameUnique) {
  auto r = Parse("module m;\n"
                 "  initial begin x = arr.unique(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, ArrayMethodNameAnd) {
  auto r = Parse("module m;\n"
                 "  initial begin x = arr.and(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, ArrayMethodNameOr) {
  auto r = Parse("module m;\n"
                 "  initial begin x = arr.or(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, ArrayMethodNameXor) {
  auto r = Parse("module m;\n"
                 "  initial begin x = arr.xor(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.2 Subroutine calls — randomize_call
// =============================================================================

// § randomize_call ::= randomize { attribute_instance }
//   [ ( [ variable_identifier_list | null ] ) ]
//   [ with [ ( [ identifier_list ] ) ] constraint_block ]

TEST(ParserA82, RandomizeCallBasic) {
  auto r = Parse("module m;\n"
                 "  initial begin obj.randomize(); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, RandomizeCallWithConstraintBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin obj.randomize() with { x < 10; }; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, RandomizeCallWithNull) {
  auto r = Parse("module m;\n"
                 "  initial begin obj.randomize(null); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, RandomizeCallWithVarList) {
  auto r = Parse("module m;\n"
                 "  initial begin obj.randomize(x, y); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § std::randomize_call (subroutine_call alternative)
TEST(ParserA82, StdRandomizeCall) {
  auto r = Parse("module m;\n"
                 "  initial begin std::randomize(x) with { x > 0; }; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.2 Subroutine calls — variable_identifier_list / identifier_list
// =============================================================================

// § variable_identifier_list ::= variable_identifier { , variable_identifier }
// § identifier_list ::= identifier { , identifier }

// Tested implicitly via randomize_call with var list above.

// variable_identifier_list in randomize
TEST(ParserA82, VariableIdentifierList) {
  auto r = Parse("module m;\n"
                 "  initial begin obj.randomize(a, b, c); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}
