// §12.4.1: if–else–if construct

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult12b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult12b Parse(const std::string& src) {
  ParseResult12b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult12b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

namespace {

TEST(ParserSection12, IfElseIfChain) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else if (c) x = 3;\n"
      "    else x = 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kIf);
}

// §12.4.1: if-else-if chain with final else
TEST(ParserA606, IfElseIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // else branch is another if statement
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  // the inner if has its own else
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kBlockingAssign);
}

// §12.4.1: multi-way if-else-if chain without final else
TEST(ParserA606, IfElseIfNoFinalElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else if (c) x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kIf);
  // last else-if has no else
  EXPECT_EQ(stmt->else_branch->else_branch->else_branch, nullptr);
}

// Chained if-else-if-else produces nested kIf on else_branch.
TEST(ParserSection12, IfElseIfElseChain) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a == 0) x = 0;\n"
      "    else if (a == 1) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->else_branch->else_branch, nullptr);
}

struct ParseResult9i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9i Parse(const std::string& src) {
  ParseResult9i result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysLatchItem(ParseResult9i& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// 5. Nested if-else chain.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_NestedIfElse) {
  auto r = Parse(
      "module m;\n"
      "  logic en1, en2, d1, d2, q;\n"
      "  always_latch\n"
      "    if (en1)\n"
      "      q <= d1;\n"
      "    else if (en2)\n"
      "      q <= d2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  // The else branch is itself an if statement.
  ASSERT_NE(item->body->else_branch, nullptr);
  EXPECT_EQ(item->body->else_branch->kind, StmtKind::kIf);
}

}  // namespace
