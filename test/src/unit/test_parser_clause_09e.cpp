#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult9e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult9e Parse(const std::string &src) {
  ParseResult9e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static Stmt *FirstInitialStmt(ParseResult9e &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.3.2 -- Parallel blocks (fork-join)
//
// This file provides extended coverage of fork...join / join_any / join_none
// parallel block constructs beyond the basics already tested in
// test_parser_clause09.cpp.
// =============================================================================

// ---------------------------------------------------------------------------
// 1. Basic fork-join with two delay-controlled statements
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkJoinTwoDelayedStmts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #5 a = 1;\n"
      "      #10 b = 2;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kDelay);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kDelay);
}

// ---------------------------------------------------------------------------
// 2. Fork-join with three parallel threads
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkJoinThreeThreads) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #5 a = 1;\n"
      "      #10 b = 2;\n"
      "      #15 c = 3;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->fork_stmts.size(), 3u);
}

// ---------------------------------------------------------------------------
// 3. Fork-join_any with two threads
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkJoinAnyTwoThreads) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #5 a = 1;\n"
      "      #100 b = 2;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
  EXPECT_EQ(stmt->fork_stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 4. Fork-join_none with a single thread
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkJoinNoneSingleThread) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #50 a = 1;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(stmt->fork_stmts.size(), 1u);
}

// ---------------------------------------------------------------------------
// 5. Named fork-join with matching end labels
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_NamedForkJoinMatchingLabels) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : thread_group\n"
      "      #10 a = 1;\n"
      "      #20 b = 2;\n"
      "    join : thread_group\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "thread_group");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
}

// ---------------------------------------------------------------------------
// 6. Named fork-join_any
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_NamedForkJoinAny) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : race_threads\n"
      "      #10 a = 1;\n"
      "      #20 b = 2;\n"
      "    join_any : race_threads\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "race_threads");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

// ---------------------------------------------------------------------------
// 7. Named fork-join_none
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_NamedForkJoinNone) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : bg_threads\n"
      "      #100 a = 1;\n"
      "    join_none : bg_threads\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "bg_threads");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

// ---------------------------------------------------------------------------
// 8. Fork with begin-end blocks as threads
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkWithBeginEndThreads) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        #10 a = 1;\n"
      "        #20 a = 2;\n"
      "      end\n"
      "      begin\n"
      "        #15 b = 3;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kBlock);
  // First block contains two delay-controlled statements
  EXPECT_EQ(stmt->fork_stmts[0]->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 9. Fork with mixed single statements and begin-end blocks
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkMixedStmtsAndBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "      begin\n"
      "        #20 b = 2;\n"
      "        #30 c = 3;\n"
      "      end\n"
      "      #40 d = 4;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 3u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kDelay);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[2]->kind, StmtKind::kDelay);
}

// ---------------------------------------------------------------------------
// 10. Fork with delay controls in threads
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkDelayControlsInThreads) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #5; #10 a = 1; end\n"
      "      begin #20 b = 2; end\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  // First thread has two delay controls inside a block
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_GE(stmt->fork_stmts[0]->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 11. Fork with event controls in threads
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkEventControlsInThreads) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      @(posedge clk) a = 1;\n"
      "      @(negedge rst) b = 0;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kEventControl);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kEventControl);
}

// ---------------------------------------------------------------------------
// 12. Nested fork inside fork
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_NestedForkInsideFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        fork\n"
      "          #5 a = 1;\n"
      "          #10 b = 2;\n"
      "        join\n"
      "      end\n"
      "      #20 c = 3;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  // First thread is a block containing a nested fork
  auto *inner_block = stmt->fork_stmts[0];
  EXPECT_EQ(inner_block->kind, StmtKind::kBlock);
  ASSERT_GE(inner_block->stmts.size(), 1u);
  EXPECT_EQ(inner_block->stmts[0]->kind, StmtKind::kFork);
  EXPECT_EQ(inner_block->stmts[0]->fork_stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 13. Fork inside begin-end inside fork
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkInBeginInFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        a = 0;\n"
      "        fork\n"
      "          #5 b = 1;\n"
      "          #10 c = 2;\n"
      "        join_none\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 1u);
  auto *block = stmt->fork_stmts[0];
  EXPECT_EQ(block->kind, StmtKind::kBlock);
  ASSERT_GE(block->stmts.size(), 2u);
  EXPECT_EQ(block->stmts[1]->kind, StmtKind::kFork);
  EXPECT_EQ(block->stmts[1]->join_kind, TokenKind::kKwJoinNone);
}

// ---------------------------------------------------------------------------
// 14. Variable declaration in fork block
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_VarDeclInFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      int x;\n"
      "      begin x = 1; end\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
}

// ---------------------------------------------------------------------------
// 15. Multiple variable declarations in fork block
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_MultipleVarDeclsInFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      int x;\n"
      "      int y;\n"
      "      begin x = 1; y = 2; end\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 3u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kVarDecl);
}

// ---------------------------------------------------------------------------
// 16. Automatic variable in fork block
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_AutomaticVarInForkBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      automatic int k = 0;\n"
      "      begin\n"
      "        k = k + 1;\n"
      "      end\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 1u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->fork_stmts[0]->var_is_automatic);
}

// ---------------------------------------------------------------------------
// 17. Fork-join_none followed by wait fork
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkJoinNoneThenWaitFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #10 a = 1; end\n"
      "      begin #20 b = 2; end\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kFork);
  EXPECT_EQ(body->stmts[0]->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

// ---------------------------------------------------------------------------
// 18. Fork-join_none followed by disable fork
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkJoinNoneThenDisableFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #100 a = 1;\n"
      "      #200 b = 2;\n"
      "    join_none\n"
      "    #50;\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kFork);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kDisableFork);
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
  auto *stmt = FirstInitialStmt(r);
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *stmt = FirstInitialStmt(r);
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
  auto *body = r.cu->modules[0]->items[0]->body;
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 1u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[0]->stmts.size(), 3u);
}

// ---------------------------------------------------------------------------
// 26. Fork with for loop as a thread
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkWithForLoop) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    fork\n"
              "      for (int i = 0; i < 4; i++) begin\n"
              "        #10 a[i] = i;\n"
              "      end\n"
              "    join\n"
              "  end\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 27. Fork-join in program block
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkJoinInProgramBlock) {
  EXPECT_TRUE(
      ParseOk("program p;\n"
              "  initial begin\n"
              "    fork\n"
              "      #10 a = 1;\n"
              "      #20 b = 2;\n"
              "    join\n"
              "  end\n"
              "endprogram\n"));
}

// ---------------------------------------------------------------------------
// 28. Fork with if-else as thread
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkWithIfElseThread) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      if (cond) a = 1; else a = 0;\n"
      "      #10 b = 2;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kDelay);
}

// ---------------------------------------------------------------------------
// 29. Named fork disabled by name
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_NamedForkDisabledByName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : my_fork\n"
      "      #100 a = 1;\n"
      "    join_none\n"
      "    #50;\n"
      "    disable my_fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  auto *fork_stmt = body->stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->label, "my_fork");
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kDisable);
}

// ---------------------------------------------------------------------------
// 30. Fork with assignment and delay in same thread
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_3_2_ForkThreadWithDelayedAssign) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        a = 0;\n"
      "        #10;\n"
      "        a = 1;\n"
      "      end\n"
      "      begin\n"
      "        b = 0;\n"
      "        #20;\n"
      "        b = 1;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  // Each thread block should contain assign, delay, assign
  for (size_t i = 0; i < 2; ++i) {
    auto *thread = stmt->fork_stmts[i];
    EXPECT_EQ(thread->kind, StmtKind::kBlock);
    EXPECT_EQ(thread->stmts.size(), 3u);
  }
}
