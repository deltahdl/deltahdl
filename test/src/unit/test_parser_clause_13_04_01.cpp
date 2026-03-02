// §13.4.1: Return values and void functions

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- data_type_or_void ---
// data_type | void
TEST(ParserA221, DataTypeOrVoidReturn) {
  // void as function return type (data_type_or_void)
  auto r = Parse(
      "module m;\n"
      "  function void do_nothing; endfunction\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

// =============================================================================
// A.2.6 Function declarations
// =============================================================================
// ---------------------------------------------------------------------------
// function_data_type_or_implicit ::=
//   data_type_or_void | implicit_data_type
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncReturnTypeExplicitInt) {
  auto r = Parse(
      "module m;\n  function int foo(); return 0; endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "foo");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(ParserA26, FuncReturnTypeVoid) {
  auto r = Parse("module m;\n  function void bar(); endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(ParserA26, FuncReturnTypeLogicPacked) {
  auto r = Parse(
      "module m;\n  function logic [3:0] baz();\n"
      "    return 4'b0;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->return_type.packed_dim_left, nullptr);
  EXPECT_NE(item->return_type.packed_dim_right, nullptr);
}

// §3.8: Function returning value, void function, all 4 argument directions.
TEST(ParserClause03, Cl3_8_FunctionReturnAndVoidAndDirections) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(input int a, output int b,\n"
      "                       inout int c, ref int d);\n"
      "    b = a;\n"
      "    return a + c + d;\n"
      "  endfunction\n"
      "  function void show(input int val);\n"
      "    $display(\"%d\", val);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl),
      2);
  const auto* compute = FindFunctionByName(r.cu->modules[0]->items, "compute");
  ASSERT_NE(compute, nullptr);
  ASSERT_EQ(compute->func_args.size(), 4u);
  EXPECT_EQ(compute->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(compute->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(compute->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(compute->func_args[3].direction, Direction::kRef);
}

struct ParseResult4e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4e Parse(const std::string& src) {
  ParseResult4e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// 17. Automatic function returning void
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncReturningVoid) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void log_msg(input int code);\n"
      "    $display(\"code=%0d\", code);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
  EXPECT_EQ(item->name, "log_msg");
}

struct ParseResult6f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6f Parse(const std::string& src) {
  ParseResult6f result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6f& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

TEST(ParserSection6, RealInFunction) {
  // §6.12: real used as function return type.
  auto r = Parse(
      "module t;\n"
      "  function real compute();\n"
      "    return 1.5;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kReal);
}

// void cast with system function call
TEST(ParserA609, VoidCastSystemCall) {
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
// LRM section 13.4.1 -- Return values and void functions (additional tests)
// =============================================================================
// Void function called as a statement (LRM 13.4.1).
TEST(ParserSection13, VoidFunctionCallAsStatement) {
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

// Void function with return type kVoid, verifying no return expr needed.
TEST(ParserSection13, VoidFunctionReturnTypeKind) {
  auto r = Parse(
      "module m;\n"
      "  function void empty_func();\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "empty_func");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kVoid);
}

// =============================================================================
// LRM section 13.4.3 -- Function calls as expressions/statements
// =============================================================================
// Function call used in a continuous assign expression.
TEST(ParserSection13, FunctionCallInContAssign) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  assign result = add(x, y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* assign = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(assign, nullptr);
  ASSERT_NE(assign->assign_rhs, nullptr);
  EXPECT_EQ(assign->assign_rhs->kind, ExprKind::kCall);
}

// Nested function calls: func(func(x)).
TEST(ParserSection13, NestedFunctionCalls) {
  auto r = Parse(
      "module m;\n"
      "  function int inc(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    y = inc(inc(a));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  // The argument to outer inc() is itself a call.
  ASSERT_EQ(stmt->rhs->args.size(), 1u);
  EXPECT_EQ(stmt->rhs->args[0]->kind, ExprKind::kCall);
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with return statement (inside function).
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockWithReturnInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int compute(input int a, input int b);\n"
              "    begin\n"
              "      int tmp;\n"
              "      tmp = a + b;\n"
              "      return tmp;\n"
              "    end\n"
              "  endfunction\n"
              "endmodule\n"));
}

// --- Packed struct as function return type ---
TEST(ParserSection7, Sec7_2_1_PackedAsFuncReturn) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] a;\n"
              "    logic [7:0] b;\n"
              "  } pair_t;\n"
              "  function pair_t make_pair;\n"
              "    input logic [7:0] x, y;\n"
              "    make_pair = {x, y};\n"
              "  endfunction\n"
              "endmodule\n"));
}

struct ParseResult12b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult12b Parse(const std::string& src) {
  ParseResult12b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// Return with complex expression.
TEST(ParserSection12, ReturnWithComplexExpr) {
  auto r = Parse(
      "module t;\n"
      "  function int compute(int a, int b);\n"
      "    return a * b + 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ret = FindReturnStmt(r);
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(ret->kind, StmtKind::kReturn);
  ASSERT_NE(ret->expr, nullptr);
  // The expression is a binary op (a * b + 1).
  EXPECT_EQ(ret->expr->kind, ExprKind::kBinary);
}

// =============================================================================
// A.8.2 Subroutine calls — tf_call
// =============================================================================
// § tf_call ::= ps_or_hierarchical_tf_identifier { attribute_instance }
//              [ ( list_of_arguments ) ]
// tf_call as expression (function return value used in RHS)
TEST(ParserA82, TfCallAsExprInAssign) {
  auto r = Parse(
      "module m;\n"
      "  initial x = func(1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->callee, "func");
  EXPECT_EQ(stmt->rhs->args.size(), 2u);
}

}  // namespace
