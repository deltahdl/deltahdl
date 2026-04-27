#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ScopeAndLifetimeParsing, DataDeclAutomaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->var_is_automatic, true);
}

TEST(ScopeAndLifetimeParsing, AutomaticVarWithExpressionInit) {
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

  EXPECT_EQ(stmt->var_init->kind, ExprKind::kBinary);
}

TEST(ScopeAndLifetimeParsing, StaticVarComplexInit) {
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

TEST(ScopeAndLifetimeParsing, BlockVarDeclNoLifetime) {
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

TEST(ScopeAndLifetimeParsing, LifetimeAutomaticAndStatic) {
  EXPECT_TRUE(ParseOk("module automatic m; endmodule\n"));
  EXPECT_TRUE(ParseOk("module static m; endmodule\n"));
  auto fa = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b); return a+b; endfunction\n"
      "endmodule\n");
  ASSERT_NE(fa.cu, nullptr);
  EXPECT_FALSE(fa.has_errors);
  EXPECT_EQ(fa.cu->modules[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(fa.cu->modules[0]->items[0]->is_automatic);
  auto fs = Parse(
      "module m;\n"
      "  function static int mul(int a, int b); return a*b; endfunction\n"
      "endmodule\n");
  ASSERT_NE(fs.cu, nullptr);
  EXPECT_FALSE(fs.has_errors);
  EXPECT_TRUE(fs.cu->modules[0]->items[0]->is_static);
  auto ta =
      Parse("module m; task automatic t(input int x); endtask endmodule\n");
  ASSERT_NE(ta.cu, nullptr);
  EXPECT_FALSE(ta.has_errors);
  EXPECT_TRUE(ta.cu->modules[0]->items[0]->is_automatic);
  auto ts = Parse("module m; task static t(input int x); endtask endmodule\n");
  ASSERT_NE(ts.cu, nullptr);
  EXPECT_FALSE(ts.has_errors);
  EXPECT_TRUE(ts.cu->modules[0]->items[0]->is_static);

  auto tl = Parse(
      "function automatic int foo(int x);\n"
      "  return x + 1;\n"
      "endfunction\n");
  ASSERT_NE(tl.cu, nullptr);
  EXPECT_FALSE(tl.has_errors);
  ASSERT_GE(tl.cu->cu_items.size(), 1u);
  EXPECT_EQ(tl.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(tl.cu->cu_items[0]->is_automatic);
  EXPECT_EQ(tl.cu->cu_items[0]->name, "foo");

  auto tt = Parse("task automatic my_task(input int x); endtask\n");
  ASSERT_NE(tt.cu, nullptr);
  EXPECT_FALSE(tt.has_errors);
  ASSERT_GE(tt.cu->cu_items.size(), 1u);
  EXPECT_EQ(tt.cu->cu_items[0]->kind, ModuleItemKind::kTaskDecl);

  EXPECT_TRUE(
      ParseOk("program automatic test_prog;\n"
              "  initial begin $display(\"hello\"); end\n"
              "endprogram\n"));
}

TEST(ScopeAndLifetimeParsing, AutomaticVarDeclInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int k = 0;\n"
      "    k = k + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(body->stmts[0]->var_is_automatic);
  EXPECT_FALSE(body->stmts[0]->var_is_static);
  EXPECT_EQ(body->stmts[0]->var_name, "k");
  EXPECT_NE(body->stmts[0]->var_init, nullptr);
}

TEST(ScopeAndLifetimeParsing, StaticVarInBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int counter = 0;\n"
      "    counter = counter + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmtT(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_static);
  EXPECT_FALSE(stmt->var_is_automatic);
  EXPECT_EQ(stmt->var_name, "counter");
}

TEST_F(ProgramParseTest, ProgramWithAutomaticLifetime) {
  auto* unit = Parse("program automatic p; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(ScopeAndLifetimeParsing, StaticBlockVarSetsFlag) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    static int st2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_static);
}

TEST(ScopeAndLifetimeParsing, StaticVarKeywordInBlock) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  initial begin\n"
               "    static var logic x;\n"
               "  end\n"
               "endmodule\n"));
}

TEST(ScopeAndLifetimeParsing, StaticVarInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static logic [7:0] saved = 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmtT(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_static);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(stmt->var_init, nullptr);
}

TEST(ScopeAndLifetimeParsing, ProgramBlockVarAutoDefault) {
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

static ModuleItem* FirstFuncOrTask(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl)
      return item;
  }
  return nullptr;
}

TEST(ScopeAndLifetimeParsing, MultipleStaticVarsInFunc) {
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

  ASSERT_GE(fn->func_body_stmts.size(), 3u);
  EXPECT_EQ(fn->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(fn->func_body_stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(fn->func_body_stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(fn->func_body_stmts[0]->var_is_static);
  EXPECT_TRUE(fn->func_body_stmts[1]->var_is_static);
  EXPECT_TRUE(fn->func_body_stmts[2]->var_is_static);
  EXPECT_EQ(fn->func_body_stmts[0]->var_name, "a");
  EXPECT_EQ(fn->func_body_stmts[1]->var_name, "b");
  EXPECT_EQ(fn->func_body_stmts[2]->var_name, "c");
}

TEST(ScopeAndLifetimeParsing, MultipleAutoVarsInFunc) {
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

TEST(ScopeAndLifetimeParsing, MixedStaticAutoInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int persist = 0;\n"
      "    automatic int scratch = 10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBodyT(r);
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

TEST(ScopeAndLifetimeParsing, StaticVarPackedDims) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static logic [15:0] wide_counter = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmtT(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_static);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(stmt->var_decl_type.packed_dim_left, nullptr);
  EXPECT_NE(stmt->var_decl_type.packed_dim_right, nullptr);
}

TEST(ScopeAndLifetimeParsing, VarInNestedBeginEnd) {
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
  auto* stmt = FirstInitialStmtT(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->stmts.size(), 1u);
  EXPECT_EQ(stmt->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->stmts[0]->var_is_automatic);
  EXPECT_EQ(stmt->stmts[0]->var_name, "inner_val");
}

static ClassMember* FindClassMethod(ParseResult& r) {
  if (r.cu->classes.empty()) return nullptr;
  for (auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kMethod) return m;
  }
  return nullptr;
}

TEST(ScopeAndLifetimeParsing, StaticVarInClassMethod) {
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
  EXPECT_EQ(r.cu->classes[0]->name, "Counter");
  auto* method_member = FindClassMethod(r);
  ASSERT_NE(method_member, nullptr);
  ASSERT_NE(method_member->method, nullptr);
  ASSERT_GE(method_member->method->func_body_stmts.size(), 1u);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->kind,
            StmtKind::kVarDecl);
  EXPECT_TRUE(method_member->method->func_body_stmts[0]->var_is_static);
}

TEST(ScopeAndLifetimeParsing, AutoVarInClassMethod) {
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
  auto* method_member = FindClassMethod(r);
  ASSERT_NE(method_member, nullptr);
  ASSERT_NE(method_member->method, nullptr);
  ASSERT_GE(method_member->method->func_body_stmts.size(), 1u);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->kind,
            StmtKind::kVarDecl);
  EXPECT_TRUE(method_member->method->func_body_stmts[0]->var_is_automatic);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->var_name, "local_data");
}

static Stmt* FirstBodyStmt(ModuleItem* item) {
  if (!item || item->func_body_stmts.empty()) return nullptr;
  return item->func_body_stmts[0];
}

TEST(ScopeAndLifetimeParsing, AutoVarInStaticFunc) {
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

TEST(ScopeAndLifetimeParsing, StaticVarInAutoFunc) {
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

TEST(ScopeAndLifetimeParsing, VarInUnnamedBlockVisibleToNested) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x = 5;\n"
      "    begin\n"
      "      x = x + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ScopeAndLifetimeParsing, CuScopeFuncStaticDefault) {
  auto r = Parse(
      "function int global_fn(int x);\n"
      "  return x + 1;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_FALSE(r.cu->cu_items[0]->is_automatic);
}

TEST(ScopeAndLifetimeParsing, LifetimeStaticOnModuleItem) {
  auto r = Parse("module m; static int x = 0; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ScopeAndLifetimeParsing, LifetimeAutomaticOnModuleItem) {
  auto r = Parse("module m; automatic int y = 0; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §6.21: A function may carry an automatic lifetime keyword, which the
// parser records on the declaration.
TEST(ScopeAndLifetimeParsing, FunctionDeclLifetimeAutomatic) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int f(); return 0; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

// §6.21: A function may also carry an explicit static lifetime keyword.
TEST(ScopeAndLifetimeParsing, FunctionDeclLifetimeStatic) {
  auto r = Parse(
      "module m;\n"
      "  function static int f(); return 0; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_TRUE(item->is_static);
}

// §6.21: A task may carry an automatic lifetime keyword.
TEST(ScopeAndLifetimeParsing, TaskDeclLifetimeAutomatic) {
  auto r = Parse(
      "module m;\n"
      "  task automatic my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

// §6.21: A task may also carry an explicit static lifetime keyword.
TEST(ScopeAndLifetimeParsing, TaskDeclLifetimeStatic) {
  auto r = Parse(
      "module m;\n"
      "  task static my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_static);
  EXPECT_FALSE(item->is_automatic);
}

}  // namespace
