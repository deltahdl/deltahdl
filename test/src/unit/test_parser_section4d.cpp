// Tests for IEEE 1800 LRM section 4.9.3 -- Reentrancy of tasks and functions
//
// Verifies that all syntactic constructs related to task/function reentrancy
// parse correctly: automatic/static lifetime qualifiers on functions and tasks,
// explicit automatic/static variables in procedural blocks, recursive function
// calls, fork-join in automatic tasks, module-level lifetime defaults, and
// program block implicit automatic lifetime.

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

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

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// Returns the first module item from the first module.
static ModuleItem* FirstItem(ParseResult4d& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// Returns the first function/task body statement from a ModuleItem.
static Stmt* FirstBodyStmt(ModuleItem* item) {
  if (!item || item->func_body_stmts.empty()) return nullptr;
  return item->func_body_stmts[0];
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
// 3. Automatic task declaration
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutomaticTaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task automatic do_work(input int n);\n"
      "    $display(\"work %0d\", n);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
  EXPECT_EQ(item->name, "do_work");
}

// =============================================================================
// 4. Static task declaration
// =============================================================================

TEST(ParserSection4, Sec4_9_3_StaticTaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task static wait_cycles(input int n);\n"
      "    repeat (n) #1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_static);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_EQ(item->name, "wait_cycles");
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

// =============================================================================
// 9. Function in program block (automatic by default)
// =============================================================================

TEST(ParserSection4, Sec4_9_3_FunctionInProgramBlock) {
  auto r = Parse(
      "program p;\n"
      "  function int get_value();\n"
      "    int local_v;\n"
      "    local_v = 42;\n"
      "    return local_v;\n"
      "  endfunction\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(r.cu->programs[0]->items.size(), 1u);
  auto* item = r.cu->programs[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "get_value");
}

// =============================================================================
// 10. Explicit automatic var in static function
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutoVarInStaticFunc) {
  auto r = Parse(
      "module m;\n"
      "  function static int process(int x);\n"
      "    automatic int temp;\n"
      "    temp = x + 1;\n"
      "    return temp;\n"
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
  EXPECT_TRUE(var_stmt->var_is_automatic);
  EXPECT_FALSE(var_stmt->var_is_static);
}

// =============================================================================
// 11. Explicit static var in automatic function
// =============================================================================

TEST(ParserSection4, Sec4_9_3_StaticVarInAutoFunc) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int accumulate(int x);\n"
      "    static int sum = 0;\n"
      "    sum = sum + x;\n"
      "    return sum;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  auto* var_stmt = FirstBodyStmt(item);
  ASSERT_NE(var_stmt, nullptr);
  EXPECT_EQ(var_stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(var_stmt->var_is_static);
  EXPECT_FALSE(var_stmt->var_is_automatic);
  EXPECT_EQ(var_stmt->var_name, "sum");
  EXPECT_NE(var_stmt->var_init, nullptr);
}

// =============================================================================
// 12. Automatic task with fork-join
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutomaticTaskWithForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  task automatic parallel_work(input int a, input int b);\n"
      "    fork\n"
      "      $display(\"a=%0d\", a);\n"
      "      $display(\"b=%0d\", b);\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  auto* fork_stmt = item->func_body_stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_GE(fork_stmt->fork_stmts.size(), 2u);
}

// =============================================================================
// 13. Automatic function with for loop variable
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutomaticFuncWithForLoop) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int sum_to_n(int n);\n"
      "    int total;\n"
      "    total = 0;\n"
      "    for (int i = 0; i < n; i = i + 1)\n"
      "      total = total + i;\n"
      "    return total;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  bool found_for = false;
  for (auto* stmt : item->func_body_stmts) {
    if (stmt->kind == StmtKind::kFor) {
      found_for = true;
      EXPECT_NE(stmt->for_cond, nullptr);
      EXPECT_NE(stmt->for_body, nullptr);
    }
  }
  EXPECT_TRUE(found_for);
}

// =============================================================================
// 14. Automatic function with multiple local vars of different types
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutoFuncMultiTypedLocalVars) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int mixed_locals(int x);\n"
      "    int a;\n"
      "    logic [7:0] b;\n"
      "    real c;\n"
      "    a = x;\n"
      "    b = x;\n"
      "    c = x;\n"
      "    return a;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 3u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[0]->var_decl_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_body_stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[1]->var_decl_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->func_body_stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[2]->var_decl_type.kind, DataTypeKind::kReal);
}

// =============================================================================
// 15. Automatic function with output argument
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutoFuncWithOutputArg) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void compute(input int a, output int b);\n"
      "    b = a * 3;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

// =============================================================================
// 16. Automatic function with ref argument
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutoFuncWithRefArg) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void swap(ref int x, ref int y);\n"
      "    int tmp;\n"
      "    tmp = x;\n"
      "    x = y;\n"
      "    y = tmp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_EQ(item->func_args[1].direction, Direction::kRef);
  EXPECT_EQ(item->func_args[1].name, "y");
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
// 19. Automatic task with delay control
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutomaticTaskWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  task automatic delayed_write(input int val);\n"
      "    #10;\n"
      "    $display(\"val=%0d\", val);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kDelay);
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

// =============================================================================
// 21. Automatic function with default argument values
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutoFuncWithDefaultArgs) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int scale(int x, int factor = 2);\n"
      "    return x * factor;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_EQ(item->func_args[0].default_value, nullptr);
  EXPECT_EQ(item->func_args[1].name, "factor");
  EXPECT_NE(item->func_args[1].default_value, nullptr);
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
// 23. Automatic function with input/output/inout ports
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutoFuncWithAllPortDirs) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void multi_dir(\n"
      "      input int a,\n"
      "      output int b,\n"
      "      inout int c);\n"
      "    b = a + c;\n"
      "    c = a;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(item->func_args[2].data_type.kind, DataTypeKind::kInt);
}

// =============================================================================
// 24. Automatic task with event control
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutoTaskWithEventControl) {
  auto r = Parse(
      "module m;\n"
      "  task automatic wait_clk(input logic clk);\n"
      "    @(posedge clk);\n"
      "    $display(\"clock edge\");\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kEventControl);
  ASSERT_FALSE(item->func_body_stmts[0]->events.empty());
  EXPECT_EQ(item->func_body_stmts[0]->events[0].edge, Edge::kPosedge);
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
// 26. Task without explicit lifetime (implicit static in module)
// =============================================================================

TEST(ParserSection4, Sec4_9_3_TaskNoLifetimeQualifier) {
  auto r = Parse(
      "module m;\n"
      "  task plain_task();\n"
      "    $display(\"hello\");\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

// =============================================================================
// 27. Module with static lifetime qualifier
// =============================================================================

TEST(ParserSection4, Sec4_9_3_StaticModuleLifetime) {
  EXPECT_TRUE(
      ParseOk("module static m;\n"
              "  function int fn();\n"
              "    return 0;\n"
              "  endfunction\n"
              "endmodule\n"));
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

// =============================================================================
// 29. Automatic function with const ref argument
// =============================================================================

TEST(ParserSection4, Sec4_9_3_AutoFuncWithConstRefArg) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int read_only(const ref int data);\n"
      "    return data;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].name, "data");
}

// =============================================================================
// 30. Task in program block (automatic by default)
// =============================================================================

TEST(ParserSection4, Sec4_9_3_TaskInProgramBlock) {
  EXPECT_TRUE(
      ParseOk("program test_prog;\n"
              "  task run_test();\n"
              "    int x;\n"
              "    x = 1;\n"
              "    $display(\"x=%0d\", x);\n"
              "  endtask\n"
              "endprogram\n"));
}
