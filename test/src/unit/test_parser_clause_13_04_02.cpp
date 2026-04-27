#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Lifetime-keyword acceptance on function declarations is a §6.21 rule;
// the corresponding parser tests (FunctionDeclLifetimeAutomatic,
// FunctionDeclLifetimeStatic, and the default-lifetime case) live in
// test_parser_clause_06_21.cpp.

TEST(FunctionLifetimeParsing, AutomaticVoidFunction) {
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

TEST(FunctionLifetimeParsing, RecursiveAutomaticFunction) {
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

TEST(FunctionLifetimeParsing, AutomaticFunctionInClass) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  function automatic int get_id();\n"
              "    return 42;\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(FunctionLifetimeParsing, MixedStaticAndAutomaticInModule) {
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

TEST(FunctionLifetimeParsing, AutomaticFunctionWithLogicReturn) {
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

static ModuleItem* FirstFuncOrTask(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl)
      return item;
  }
  return nullptr;
}

TEST(FunctionLifetimeParsing, StaticFunctionWithLocalVar) {
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

TEST(FunctionLifetimeParsing, StaticVarInAutomaticFunction) {
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

TEST(FunctionLifetimeParsing, AutomaticVarInStaticFunction) {
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

TEST(FunctionLifetimeParsing, AutomaticFunctionWithLocalVars) {
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

static Stmt* FirstBodyStmt(ModuleItem* item) {
  if (!item || item->func_body_stmts.empty()) return nullptr;
  return item->func_body_stmts[0];
}

TEST(FunctionLifetimeParsing, StaticFunctionWithStaticLocalVar) {
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

TEST(FunctionLifetimeParsing, FunctionInAutomaticModule) {
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

  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(FunctionLifetimeParsing, FunctionInProgramBlock) {
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

TEST(FunctionLifetimeParsing, AutomaticFunctionMultipleVarTypes) {
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

TEST(FunctionLifetimeParsing, FunctionInInterface) {
  auto r = Parse(
      "interface bus;\n"
      "  function int get_data();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "get_data");
}

}  // namespace
