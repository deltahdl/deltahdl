// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

static ClassMember* FindClassMethod(ParseResult4e& r) {
  if (r.cu->classes.empty()) return nullptr;
  for (auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kMethod) return m;
  }
  return nullptr;
}

namespace {

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
  auto* stmt = FirstInitialStmtT(r);
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
  auto* stmt = FirstInitialStmtT(r);
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
  auto* for_stmt = FindStmtByKind(fn, StmtKind::kFor);
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
  auto* for_stmt = FindStmtByKind(fn, StmtKind::kFor);
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
  EXPECT_EQ(r.cu->classes[0]->name, "Counter");
  auto* method_member = FindClassMethod(r);
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
  auto* method_member = FindClassMethod(r);
  ASSERT_NE(method_member, nullptr);
  ASSERT_NE(method_member->method, nullptr);
  ASSERT_GE(method_member->method->func_body_stmts.size(), 1u);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->kind,
            StmtKind::kVarDecl);
  EXPECT_TRUE(method_member->method->func_body_stmts[0]->var_is_automatic);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->var_name, "local_data");
}

}  // namespace
