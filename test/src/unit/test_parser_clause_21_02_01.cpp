// §21.2.1: The display and write tasks

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DisplayInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg clk;\n"
              "  always @(posedge clk)\n"
              "    $display(\"clock edge at %0t\", $time);\n"
              "endmodule\n"));
}

struct ParseResult4b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static Stmt* FirstInitialStmt(ParseResult4b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 8. $display system call (Active region)
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_DisplaySystemCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$display");
}

struct ParseResult11d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11d Parse(const std::string& src) {
  ParseResult11d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// --- Empty args in system calls (§20.2/§21.2) ---
TEST(ParserSection11, SystemCallEmptyArgs) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(5,,2,,3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, SystemCallLeadingEmptyArg) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(,\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ============================================================================
// AST-level checks for system calls in initial blocks
// ============================================================================
TEST(ParserSection21, DisplayParsesAsSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
}

// ============================================================================
// LRM section 21.1 -- Display system tasks (general I/O overview)
// ============================================================================
TEST(ParserSection21, DisplayBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"hello\");\n"
              "endmodule\n"));
}

TEST(ParserSection21, DisplayNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display;\n"
              "endmodule\n"));
}

TEST(ParserSection21, DisplayMultipleArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"x=%d y=%h\", x, y);\n"
              "endmodule\n"));
}

TEST(ParserSection21, WriteBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $write(\"no newline\");\n"
              "endmodule\n"));
}

TEST(ParserSection21, WriteNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $write;\n"
              "endmodule\n"));
}

}  // namespace
