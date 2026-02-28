// §6.21: Scope and lifetime

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- lifetime ---
// static | automatic
TEST(ParserA213, LifetimeStaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int x;\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, LifetimeAutomaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int y;\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA28, DataDeclAutomaticInBlock) {
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

TEST(ParserA28, DataDeclStaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->var_is_static, true);
}

static Stmt* InitialBody(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    return item->body;
  }
  return nullptr;
}

// §6.21: Sequential block with automatic lifetime variable
TEST(ParserA603, SeqBlockWithAutomaticVar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int k = 10;\n"
      "    a = k;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(body->stmts[0]->var_is_automatic);
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

static Stmt* FirstInitialStmt(ParseResult50603& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
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

struct ParseResult7 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult7 Parse(const std::string& src) {
  ParseResult7 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// LRM section 6.21 -- Scope and lifetime (automatic/static)
// =============================================================================
TEST(ParserSection6, Sec6_21_LifetimeAutomaticAndStatic) {
  // Module lifetime qualifiers
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
  // Top-level function with automatic lifetime
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
  // Top-level task in compilation-unit scope
  auto tt = Parse("task automatic my_task(input int x); endtask\n");
  ASSERT_NE(tt.cu, nullptr);
  EXPECT_FALSE(tt.has_errors);
  ASSERT_GE(tt.cu->cu_items.size(), 1u);
  EXPECT_EQ(tt.cu->cu_items[0]->kind, ModuleItemKind::kTaskDecl);
  // Program with automatic lifetime
  EXPECT_TRUE(
      ParseOk("program automatic test_prog;\n"
              "  initial begin $display(\"hello\"); end\n"
              "endprogram\n"));
}

struct ParseResult9e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9e Parse(const std::string& src) {
  ParseResult9e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 9.3.1 -- Automatic and static variable declarations in blocks.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_AutomaticVarDeclInBlock) {
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

}  // namespace
