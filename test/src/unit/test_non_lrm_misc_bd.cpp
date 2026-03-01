// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

static Stmt* FindStmtByKind(ModuleItem* item, StmtKind kind) {
  for (auto* stmt : item->func_body_stmts) {
    if (stmt->kind == kind) return stmt;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §4.6: Program block with clocking block reference
// =============================================================================
TEST(ParserSection4, Sec4_6_ProgramWithClockingBlock) {
  EXPECT_TRUE(
      ParseOk("program p(input logic clk);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    output valid;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    @(cb);\n"
              "    $display(\"synced\");\n"
              "  end\n"
              "endprogram\n"));
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
  auto* for_stmt = FindStmtByKind(item, StmtKind::kFor);
  ASSERT_NE(for_stmt, nullptr);
  EXPECT_NE(for_stmt->for_cond, nullptr);
  EXPECT_NE(for_stmt->for_body, nullptr);
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

}  // namespace
