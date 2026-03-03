// §9.3.2: Parallel blocks

#include "fixture_parser.h"

using namespace delta;

namespace {

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
  auto* stmt = FirstInitialStmtT(r);
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

// §9.3.2: par_block (fork-join)
TEST(ParserA604, StmtItemParBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
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

static Stmt* FirstInitialStmt(ParseResult9e& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// 19. Empty fork-join block
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_EmptyForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_TRUE(stmt->fork_stmts.empty());
}

// ---------------------------------------------------------------------------
// 20. Fork in task body
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_ForkInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task automatic run_parallel;\n"
              "    fork\n"
              "      #10 a = 1;\n"
              "      #20 b = 2;\n"
              "    join\n"
              "  endtask\n"
              "  initial run_parallel;\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 21. Fork in always block
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_ForkInAlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) begin\n"
      "    fork\n"
      "      #1 a = 1;\n"
      "      #2 b = 2;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kFork);
  EXPECT_EQ(item->body->stmts[0]->join_kind, TokenKind::kKwJoinNone);
}

}  // namespace
