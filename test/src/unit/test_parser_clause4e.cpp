// Tests for IEEE 1800 LRM section 4.9.4 -- Static and automatic variables
//
// Verifies that all syntactic constructs related to static and automatic
// variable lifetimes parse correctly: explicit lifetime qualifiers on
// functions/tasks, block-level variable declarations with lifetime, for-loop
// init variables, program block default lifetime, class method variables, and
// mixed lifetime declarations within the same scope.

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

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

// Returns the first statement inside the first initial block's begin-end.
static Stmt* FirstInitialStmt(ParseResult4e& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// Returns the body of the first initial block.
static Stmt* InitialBody(ParseResult4e& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) return item->body;
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
// 7. Static variable in begin-end block (initial block)
// =============================================================================

TEST(ParserSection4, Sec4_9_4_StaticVarInBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int counter = 0;\n"
      "    counter = counter + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_static);
  EXPECT_FALSE(stmt->var_is_automatic);
  EXPECT_EQ(stmt->var_name, "counter");
}

// =============================================================================
// 8. Automatic variable in begin-end block (initial block)
// =============================================================================

TEST(ParserSection4, Sec4_9_4_AutoVarInBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int temp = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_automatic);
  EXPECT_FALSE(stmt->var_is_static);
  EXPECT_EQ(stmt->var_name, "temp");
  EXPECT_NE(stmt->var_init, nullptr);
}

// =============================================================================
// 9. Automatic variable in fork block
// =============================================================================

TEST(ParserSection4, Sec4_9_4_AutoVarInForkBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        automatic int tid = 1;\n"
      "      end\n"
      "      begin\n"
      "        automatic int tid = 2;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  // First fork branch: begin-end block with automatic var decl.
  auto* branch0 = stmt->fork_stmts[0];
  ASSERT_EQ(branch0->kind, StmtKind::kBlock);
  ASSERT_GE(branch0->stmts.size(), 1u);
  EXPECT_EQ(branch0->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(branch0->stmts[0]->var_is_automatic);
}

// =============================================================================
// 10. For loop variable declaration
// =============================================================================

TEST(ParserSection4, Sec4_9_4_ForLoopVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) begin\n"
      "      $display(i);\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

// =============================================================================
// 11. Static variable in initial block (no function)
// =============================================================================

TEST(ParserSection4, Sec4_9_4_StaticVarInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static logic [7:0] saved = 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_static);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(stmt->var_init, nullptr);
}

// =============================================================================
// 12. Variable in program block (automatic by default)
// =============================================================================

TEST(ParserSection4, Sec4_9_4_ProgramBlockVarAutoDefault) {
  auto r = Parse(
      "program p;\n"
      "  initial begin\n"
      "    int x = 5;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

// =============================================================================
// 13. Multiple static vars in same function
// =============================================================================

TEST(ParserSection4, Sec4_9_4_MultipleStaticVarsInFunc) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void multi_static();\n"
      "    static int a = 0;\n"
      "    static int b = 0;\n"
      "    static int c = 0;\n"
      "    a = a + 1;\n"
      "    b = b + 2;\n"
      "    c = c + 3;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_automatic);
  // First three statements should be static variable declarations.
  ASSERT_GE(fn->func_body_stmts.size(), 3u);
  for (int i = 0; i < 3; ++i) {
    EXPECT_EQ(fn->func_body_stmts[i]->kind, StmtKind::kVarDecl);
    EXPECT_TRUE(fn->func_body_stmts[i]->var_is_static);
  }
  EXPECT_EQ(fn->func_body_stmts[0]->var_name, "a");
  EXPECT_EQ(fn->func_body_stmts[1]->var_name, "b");
  EXPECT_EQ(fn->func_body_stmts[2]->var_name, "c");
}

// =============================================================================
// 14. Multiple automatic vars in same function
// =============================================================================

TEST(ParserSection4, Sec4_9_4_MultipleAutoVarsInFunc) {
  auto r = Parse(
      "module m;\n"
      "  function static void multi_auto(int x);\n"
      "    automatic int p = x + 1;\n"
      "    automatic int q = x + 2;\n"
      "    $display(p, q);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_static);
  ASSERT_GE(fn->func_body_stmts.size(), 2u);
  EXPECT_EQ(fn->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(fn->func_body_stmts[0]->var_is_automatic);
  EXPECT_EQ(fn->func_body_stmts[0]->var_name, "p");
  EXPECT_EQ(fn->func_body_stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(fn->func_body_stmts[1]->var_is_automatic);
  EXPECT_EQ(fn->func_body_stmts[1]->var_name, "q");
}

// =============================================================================
// 15. Mixed static and automatic vars in same block
// =============================================================================

TEST(ParserSection4, Sec4_9_4_MixedStaticAutoInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int persist = 0;\n"
      "    automatic int scratch = 10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(body->stmts[0]->var_is_static);
  EXPECT_EQ(body->stmts[0]->var_name, "persist");
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(body->stmts[1]->var_is_automatic);
  EXPECT_EQ(body->stmts[1]->var_name, "scratch");
}

// =============================================================================
// 16. Static task declaration
// =============================================================================

TEST(ParserSection4, Sec4_9_4_StaticTaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task static log_event(input int code);\n"
      "    $display(\"event: %0d\", code);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* t = FirstFuncOrTask(r);
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(t->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(t->is_static);
  EXPECT_FALSE(t->is_automatic);
  EXPECT_EQ(t->name, "log_event");
}

// =============================================================================
// 17. Automatic task with automatic local vars (different types)
// =============================================================================

TEST(ParserSection4, Sec4_9_4_AutoTaskWithVariousTypes) {
  auto r = Parse(
      "module m;\n"
      "  task automatic process();\n"
      "    int i_val;\n"
      "    logic [3:0] l_val;\n"
      "    real r_val;\n"
      "    i_val = 1;\n"
      "    l_val = 4'hA;\n"
      "    r_val = 3.14;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* t = FirstFuncOrTask(r);
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(t->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(t->is_automatic);
  EXPECT_EQ(t->name, "process");
  // The local variable declarations should be present as func_body_stmts.
  ASSERT_GE(t->func_body_stmts.size(), 3u);
  EXPECT_EQ(t->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(t->func_body_stmts[0]->var_decl_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(t->func_body_stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(t->func_body_stmts[1]->var_decl_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(t->func_body_stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(t->func_body_stmts[2]->var_decl_type.kind, DataTypeKind::kReal);
}

// =============================================================================
// 18. Static variable with packed dimensions
// =============================================================================

TEST(ParserSection4, Sec4_9_4_StaticVarPackedDims) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static logic [15:0] wide_counter = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_static);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(stmt->var_decl_type.packed_dim_left, nullptr);
  EXPECT_NE(stmt->var_decl_type.packed_dim_right, nullptr);
}

// =============================================================================
// 19. Static function with static local and return
// =============================================================================

TEST(ParserSection4, Sec4_9_4_StaticFuncWithStaticLocal) {
  auto r = Parse(
      "module m;\n"
      "  function static int get_seq();\n"
      "    int seq_num;\n"
      "    seq_num = seq_num + 1;\n"
      "    return seq_num;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_static);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kInt);
  ASSERT_GE(fn->func_body_stmts.size(), 1u);
  EXPECT_EQ(fn->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(fn->func_body_stmts[0]->var_name, "seq_num");
}

// =============================================================================
// 20. Automatic task with explicit automatic local vars
// =============================================================================

TEST(ParserSection4, Sec4_9_4_AutoTaskExplicitAutoLocals) {
  auto r = Parse(
      "module m;\n"
      "  task automatic run(input int seed);\n"
      "    automatic int local_seed = seed;\n"
      "    $display(local_seed);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* t = FirstFuncOrTask(r);
  ASSERT_NE(t, nullptr);
  EXPECT_TRUE(t->is_automatic);
  ASSERT_GE(t->func_body_stmts.size(), 1u);
  EXPECT_EQ(t->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(t->func_body_stmts[0]->var_is_automatic);
  EXPECT_EQ(t->func_body_stmts[0]->var_name, "local_seed");
  EXPECT_NE(t->func_body_stmts[0]->var_init, nullptr);
}

// =============================================================================
// 21. Variable in nested begin-end block
// =============================================================================

TEST(ParserSection4, Sec4_9_4_VarInNestedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      automatic int inner_val = 7;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->stmts.size(), 1u);
  EXPECT_EQ(stmt->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->stmts[0]->var_is_automatic);
  EXPECT_EQ(stmt->stmts[0]->var_name, "inner_val");
}

// =============================================================================
// 22. For-loop init var in static function
// =============================================================================

TEST(ParserSection4, Sec4_9_4_ForLoopInitInStaticFunc) {
  auto r = Parse(
      "module m;\n"
      "  function static int sum_n(int n);\n"
      "    int total;\n"
      "    total = 0;\n"
      "    for (int i = 0; i < n; i = i + 1)\n"
      "      total = total + i;\n"
      "    return total;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_static);
  // Find the for-loop statement in the function body.
  Stmt* for_stmt = nullptr;
  for (auto* s : fn->func_body_stmts) {
    if (s->kind == StmtKind::kFor) {
      for_stmt = s;
      break;
    }
  }
  ASSERT_NE(for_stmt, nullptr);
  EXPECT_EQ(for_stmt->for_init_type.kind, DataTypeKind::kInt);
}

// =============================================================================
// 23. For-loop init var in automatic function
// =============================================================================

TEST(ParserSection4, Sec4_9_4_ForLoopInitInAutoFunc) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int sum_auto(int n);\n"
      "    int total = 0;\n"
      "    for (int i = 0; i < n; i = i + 1)\n"
      "      total = total + i;\n"
      "    return total;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_automatic);
  Stmt* for_stmt = nullptr;
  for (auto* s : fn->func_body_stmts) {
    if (s->kind == StmtKind::kFor) {
      for_stmt = s;
      break;
    }
  }
  ASSERT_NE(for_stmt, nullptr);
  EXPECT_EQ(for_stmt->for_init_type.kind, DataTypeKind::kInt);
}

// =============================================================================
// 24. Static var in class method
// =============================================================================

TEST(ParserSection4, Sec4_9_4_StaticVarInClassMethod) {
  auto r = Parse(
      "class Counter;\n"
      "  function int next();\n"
      "    static int id = 0;\n"
      "    id = id + 1;\n"
      "    return id;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "Counter");
  // Find the method member.
  ClassMember* method_member = nullptr;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      method_member = m;
      break;
    }
  }
  ASSERT_NE(method_member, nullptr);
  ASSERT_NE(method_member->method, nullptr);
  ASSERT_GE(method_member->method->func_body_stmts.size(), 1u);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->kind,
            StmtKind::kVarDecl);
  EXPECT_TRUE(method_member->method->func_body_stmts[0]->var_is_static);
}

// =============================================================================
// 25. Automatic var in class method
// =============================================================================

TEST(ParserSection4, Sec4_9_4_AutoVarInClassMethod) {
  auto r = Parse(
      "class Worker;\n"
      "  task run();\n"
      "    automatic int local_data = 42;\n"
      "    $display(local_data);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ClassMember* method_member = nullptr;
  for (auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      method_member = m;
      break;
    }
  }
  ASSERT_NE(method_member, nullptr);
  ASSERT_NE(method_member->method, nullptr);
  ASSERT_GE(method_member->method->func_body_stmts.size(), 1u);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->kind,
            StmtKind::kVarDecl);
  EXPECT_TRUE(method_member->method->func_body_stmts[0]->var_is_automatic);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->var_name, "local_data");
}

// =============================================================================
// 26. Variable declaration with assignment in block
// =============================================================================

TEST(ParserSection4, Sec4_9_4_VarDeclWithAssignInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int val = 2 + 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_automatic);
  EXPECT_EQ(stmt->var_name, "val");
  ASSERT_NE(stmt->var_init, nullptr);
  // The initializer should be a binary expression (2 + 3).
  EXPECT_EQ(stmt->var_init->kind, ExprKind::kBinary);
}

// =============================================================================
// 27. Static var with complex initializer expression
// =============================================================================

TEST(ParserSection4, Sec4_9_4_StaticVarComplexInit) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int calc();\n"
      "    static int base = (10 * 20) + 5;\n"
      "    return base;\n"
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
  EXPECT_EQ(var_stmt->var_name, "base");
  ASSERT_NE(var_stmt->var_init, nullptr);
  EXPECT_EQ(var_stmt->var_init->kind, ExprKind::kBinary);
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
// 29. Block-level var decl without explicit lifetime (plain int in block)
// =============================================================================

TEST(ParserSection4, Sec4_9_4_BlockVarDeclNoLifetime) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int plain_var = 99;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_FALSE(stmt->var_is_static);
  EXPECT_FALSE(stmt->var_is_automatic);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(stmt->var_name, "plain_var");
  EXPECT_NE(stmt->var_init, nullptr);
}

// =============================================================================
// 30. Program block with function parses
// =============================================================================

TEST(ParserSection4, Sec4_9_4_ProgramWithFunction) {
  EXPECT_TRUE(
      ParseOk("program p;\n"
              "  function automatic int get_val();\n"
              "    automatic int v = 10;\n"
              "    return v;\n"
              "  endfunction\n"
              "  initial begin\n"
              "    $display(get_val());\n"
              "  end\n"
              "endprogram\n"));
}
