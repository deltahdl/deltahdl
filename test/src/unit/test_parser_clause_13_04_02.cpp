// §13.4.2: Static and automatic functions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2FunctionDeclAutomaticParse) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "add");
}

TEST(ParserAnnexA, A2FunctionDeclAutomaticProps) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->func_args.size(), 2u);
}

TEST(ParserA213, LifetimeInFunction) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int calc; return 0; endfunction\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_automatic);
}

// ---------------------------------------------------------------------------
// function_declaration ::=
//   function [ dynamic_override_specifiers ] [ lifetime ]
//     function_body_declaration
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncLifetimeAutomatic) {
  auto r = Parse(
      "module m;\n  function automatic int foo();\n"
      "    return 1;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(ParserA26, FuncLifetimeStatic) {
  auto r = Parse(
      "module m;\n  function static int foo();\n"
      "    return 1;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserA26, FuncLifetimeDefault) {
  auto r = Parse(
      "module m;\n  function int foo();\n"
      "    return 1;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
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
// 18. Recursive automatic function with base case (Fibonacci)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_RecursiveAutoFuncFibonacci) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int fibonacci(int n);\n"
      "    if (n == 0)\n"
      "      return 0;\n"
      "    else if (n == 1)\n"
      "      return 1;\n"
      "    else\n"
      "      return fibonacci(n - 1) + fibonacci(n - 2);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->name, "fibonacci");
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kIf);
  EXPECT_NE(item->func_body_stmts[0]->else_branch, nullptr);
}

// =============================================================================
// 20. Automatic function in class context
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncInClass) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  function automatic int get_id();\n"
              "    return 42;\n"
              "  endfunction\n"
              "endclass\n"));
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
struct ParseResult50603 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50603 Parse(const std::string& src) {
  ParseResult50603 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// 28. Function without explicit lifetime (default — static in module)
// =============================================================================
TEST(ParserSection4, Sec4_9_4_FuncNoExplicitLifetime) {
  auto r = Parse(
      "module m;\n"
      "  function int adder(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->kind, ModuleItemKind::kFunctionDecl);
  // No explicit lifetime — both flags should be false.
  EXPECT_FALSE(fn->is_static);
  EXPECT_FALSE(fn->is_automatic);
  EXPECT_EQ(fn->name, "adder");
}

// =============================================================================
// 22. Mixed static and automatic functions in same module
// =============================================================================
TEST(ParserSection4, Sec4_9_3_MixedStaticAutoFuncsInModule) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int auto_fn(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  function static int static_fn(int x);\n"
      "    return x - 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* auto_fn = r.cu->modules[0]->items[0];
  auto* static_fn = r.cu->modules[0]->items[1];
  EXPECT_TRUE(auto_fn->is_automatic);
  EXPECT_FALSE(auto_fn->is_static);
  EXPECT_TRUE(static_fn->is_static);
  EXPECT_FALSE(static_fn->is_automatic);
}

// =============================================================================
// 25. Function without explicit lifetime (implicit static in module)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_FuncNoLifetimeQualifier) {
  auto r = Parse(
      "module m;\n"
      "  function int plain_fn(int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

// =============================================================================
// 28. Automatic function returning logic with packed dimensions
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncReturningLogic) {
  auto r = Parse(
      "module m;\n"
      "  function automatic logic [7:0] get_byte(int idx);\n"
      "    return idx;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->return_type.packed_dim_left, nullptr);
  EXPECT_NE(item->return_type.packed_dim_right, nullptr);
}

// Returns the first function or task declaration from the first module.
static ModuleItem* FirstFuncOrTask(ParseResult4e& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl)
      return item;
  }
  return nullptr;
}

// =============================================================================
// 1. Static function — variables are static by default
// =============================================================================
TEST(ParserSection4, Sec4_9_4_StaticFunctionDecl) {
  auto r = Parse(
      "module m;\n"
      "  function static int count();\n"
      "    int c;\n"
      "    c = c + 1;\n"
      "    return c;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(fn->is_static);
  EXPECT_FALSE(fn->is_automatic);
  EXPECT_EQ(fn->name, "count");
}

// =============================================================================
// 2. Automatic function — variables are automatic by default
// =============================================================================
TEST(ParserSection4, Sec4_9_4_AutomaticFunctionDecl) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(fn->is_automatic);
  EXPECT_FALSE(fn->is_static);
  EXPECT_EQ(fn->name, "factorial");
}

// =============================================================================
// 3. Explicit static variable in automatic function
// =============================================================================
TEST(ParserSection4, Sec4_9_4_ExplicitStaticInAutoFunc) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int call_count();\n"
      "    static int cnt = 0;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_automatic);
  ASSERT_GE(fn->func_body_stmts.size(), 1u);
  EXPECT_EQ(fn->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(fn->func_body_stmts[0]->var_is_static);
  EXPECT_FALSE(fn->func_body_stmts[0]->var_is_automatic);
  EXPECT_EQ(fn->func_body_stmts[0]->var_name, "cnt");
}

// =============================================================================
// 4. Explicit automatic variable in static function
// =============================================================================
TEST(ParserSection4, Sec4_9_4_ExplicitAutoInStaticFunc) {
  auto r = Parse(
      "module m;\n"
      "  function static int compute(int x);\n"
      "    automatic int tmp = x * 2;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_static);
  ASSERT_GE(fn->func_body_stmts.size(), 1u);
  EXPECT_EQ(fn->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(fn->func_body_stmts[0]->var_is_automatic);
  EXPECT_FALSE(fn->func_body_stmts[0]->var_is_static);
  EXPECT_EQ(fn->func_body_stmts[0]->var_name, "tmp");
}

struct ParseResult4d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4d Parse(const std::string& src) {
  ParseResult4d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §4.6: Static vs automatic function lifetime
// =============================================================================
TEST(ParserSection4, Sec4_6_StaticVsAutomaticFunctionLifetime) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int auto_fn();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  function static int static_fn();\n"
      "    return 2;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* auto_fn = r.cu->modules[0]->items[0];
  auto* static_fn = r.cu->modules[0]->items[1];
  EXPECT_EQ(auto_fn->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(auto_fn->is_automatic);
  EXPECT_FALSE(auto_fn->is_static);
  EXPECT_EQ(static_fn->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(static_fn->is_static);
  EXPECT_FALSE(static_fn->is_automatic);
}

// Returns the first module item from the first module.
static ModuleItem* FirstItem(ParseResult4d& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// =============================================================================
// 1. Automatic function declaration parses (function automatic ...)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticFunctionDecl) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
  EXPECT_EQ(item->name, "add");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

// =============================================================================
// 5. Static variable with initializer in function
// =============================================================================
TEST(ParserSection4, Sec4_9_4_StaticVarWithInitInFunc) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int get_id();\n"
      "    static int next_id = 100;\n"
      "    next_id = next_id + 1;\n"
      "    return next_id;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  ASSERT_GE(fn->func_body_stmts.size(), 1u);
  auto* var_stmt = fn->func_body_stmts[0];
  EXPECT_EQ(var_stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(var_stmt->var_is_static);
  EXPECT_EQ(var_stmt->var_name, "next_id");
  EXPECT_NE(var_stmt->var_init, nullptr);
}

// =============================================================================
// 2. Static function declaration parses (function static ...)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_StaticFunctionDecl) {
  auto r = Parse(
      "module m;\n"
      "  function static int counter();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_static);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_EQ(item->name, "counter");
}

// =============================================================================
// 6. Automatic variable with initializer in function
// =============================================================================
TEST(ParserSection4, Sec4_9_4_AutoVarWithInitInFunc) {
  auto r = Parse(
      "module m;\n"
      "  function static int compute(int a, int b);\n"
      "    automatic int result = a + b;\n"
      "    return result;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  ASSERT_GE(fn->func_body_stmts.size(), 1u);
  auto* var_stmt = fn->func_body_stmts[0];
  EXPECT_EQ(var_stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(var_stmt->var_is_automatic);
  EXPECT_EQ(var_stmt->var_name, "result");
  EXPECT_NE(var_stmt->var_init, nullptr);
}

// =============================================================================
// 5. Automatic function with local variable declarations
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticFuncWithLocalVars) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int compute(int x);\n"
      "    int temp;\n"
      "    int result;\n"
      "    temp = x * 2;\n"
      "    result = temp + 1;\n"
      "    return result;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 2u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[1]->kind, StmtKind::kVarDecl);
}

// =============================================================================
// 6. Automatic function with recursive call (factorial)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticFuncRecursiveCall) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1)\n"
      "      return 1;\n"
      "    else\n"
      "      return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->name, "factorial");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kIf);
}

// Returns the first function/task body statement from a ModuleItem.
static Stmt* FirstBodyStmt(ModuleItem* item) {
  if (!item || item->func_body_stmts.empty()) return nullptr;
  return item->func_body_stmts[0];
}

// =============================================================================
// 7. Static function with static local variable
// =============================================================================
TEST(ParserSection4, Sec4_9_3_StaticFuncWithStaticLocalVar) {
  auto r = Parse(
      "module m;\n"
      "  function static int call_count();\n"
      "    static int cnt = 0;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_static);
  auto* var_stmt = FirstBodyStmt(item);
  ASSERT_NE(var_stmt, nullptr);
  EXPECT_EQ(var_stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(var_stmt->var_is_static);
  EXPECT_FALSE(var_stmt->var_is_automatic);
  EXPECT_NE(var_stmt->var_init, nullptr);
}

// =============================================================================
// 8. Automatic function in automatic module
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticFuncInAutoModule) {
  auto r = Parse(
      "module automatic m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "add");
  // In an automatic module, functions without explicit qualifier inherit
  // automatic lifetime; the parser accepts this but does not set the flag
  // on the function itself (that is a semantic concern).
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

}  // namespace
