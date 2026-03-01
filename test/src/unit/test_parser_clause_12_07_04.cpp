// §12.7.4: The while-loop

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9h Parse(const std::string& src) {
  ParseResult9h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// ---------------------------------------------------------------------------
// 9. always_comb with while loop
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] val;\n"
      "  logic [3:0] count;\n"
      "  always_comb begin\n"
      "    count = 0;\n"
      "    while (val[count] && count < 8)\n"
      "      count = count + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kWhile);
}

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

// Nested loops: for inside while.
TEST(ParserSection12, NestedForInsideWhile) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    while (running) begin\n"
      "      for (int i = 0; i < 8; i = i + 1)\n"
      "        data[i] = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->body->stmts.size(), 1u);
  EXPECT_EQ(stmt->body->stmts[0]->kind, StmtKind::kFor);
}

// While loop with null body (semicolon).
TEST(ParserSection12, WhileWithNullBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    while (0) ;\n"
              "  end\n"
              "endmodule\n"));
}

// --- while ( expression ) statement_or_null ---
TEST(ParserA608, WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin while (x > 0) x = x - 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

}  // namespace
