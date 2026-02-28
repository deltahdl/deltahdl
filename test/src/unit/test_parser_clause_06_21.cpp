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

}  // namespace
