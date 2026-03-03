// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

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

namespace {

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

// ---------------------------------------------------------------------------
// 22. Fork with nonblocking assignments
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_ForkWithNonblockingAssigns) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a <= 1;\n"
      "      b <= 2;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kNonblockingAssign);
}

// ---------------------------------------------------------------------------
// 23. Multiple sequential fork blocks
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_MultipleSequentialForks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #5 a = 1;\n"
      "    join\n"
      "    fork\n"
      "      #10 b = 2;\n"
      "    join\n"
      "    fork\n"
      "      #15 c = 3;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kFork);
  EXPECT_EQ(body->stmts[0]->join_kind, TokenKind::kKwJoin);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kFork);
  EXPECT_EQ(body->stmts[1]->join_kind, TokenKind::kKwJoin);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kFork);
  EXPECT_EQ(body->stmts[2]->join_kind, TokenKind::kKwJoinAny);
}

// ---------------------------------------------------------------------------
// 24. Fork with system calls ($display, $finish)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_ForkWithSystemCalls) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    fork\n"
              "      $display(\"thread 1\");\n"
              "      $display(\"thread 2\");\n"
              "    join\n"
              "  end\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 25. Fork-join with single begin-end thread
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_ForkJoinSingleBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        a = 1;\n"
      "        b = 2;\n"
      "        c = 3;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 1u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[0]->stmts.size(), 3u);
}

}  // namespace
