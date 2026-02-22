#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt *InitialBody(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    return item->body;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.6.3 Parallel and sequential blocks
// =============================================================================

// ---------------------------------------------------------------------------
// seq_block: begin...end
// ---------------------------------------------------------------------------

// §9.3.1: Basic sequential block
TEST(ParserA603, SeqBlockBasic) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a = 1;\n"
                 "    b = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts.size(), 2u);
}

// §9.3.1: Empty sequential block
TEST(ParserA603, SeqBlockEmpty) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts.size(), 0u);
}

// §9.3.4: Named sequential block
TEST(ParserA603, SeqBlockNamed) {
  auto r = Parse("module m;\n"
                 "  initial begin : my_block\n"
                 "    a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

// §9.3.4: Named sequential block with matching end label
TEST(ParserA603, SeqBlockNamedWithEndLabel) {
  auto r = Parse("module m;\n"
                 "  initial begin : blockB\n"
                 "    a = 1;\n"
                 "  end : blockB\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "blockB");
}

// §A.2.8: Sequential block with block_item_declaration (variable)
TEST(ParserA603, SeqBlockWithVarDecl) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    int x;\n"
                 "    x = 5;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

// §6.21: Sequential block with automatic lifetime variable
TEST(ParserA603, SeqBlockWithAutomaticVar) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    automatic int k = 10;\n"
                 "    a = k;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(body->stmts[0]->var_is_automatic);
}

// §9.3.1: Nested sequential blocks
TEST(ParserA603, SeqBlockNested) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    begin\n"
                 "      a = 1;\n"
                 "    end\n"
                 "    begin\n"
                 "      b = 2;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
}

// §A.2.8: Sequential block with parameter declaration
TEST(ParserA603, SeqBlockWithParamDecl) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    parameter int P = 42;\n"
                 "    a = P;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_GE(body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// par_block: fork...join_keyword
// ---------------------------------------------------------------------------

// §9.3.2: Basic fork...join
TEST(ParserA603, ForkJoin) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork #10 a = 1; #20 b = 1; join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_EQ(stmt->fork_stmts.size(), 2u);
}

// §9.3.2: fork...join_any
TEST(ParserA603, ForkJoinAny) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork #10 a = 1; join_any\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

// §9.3.2: fork...join_none
TEST(ParserA603, ForkJoinNone) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork #10 a = 1; join_none\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

// §9.3.2: Empty fork...join
TEST(ParserA603, ForkJoinEmpty) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->fork_stmts.size(), 0u);
}

// §9.3.4: Named fork block
TEST(ParserA603, ForkNamed) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork : my_fork\n"
                 "      #10 a = 1;\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "my_fork");
}

// §9.3.4: Named fork block with matching end label
TEST(ParserA603, ForkNamedWithEndLabel) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork : my_fork\n"
                 "      #10 a = 1;\n"
                 "    join : my_fork\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->label, "my_fork");
}

// §9.3.4: Named fork with join_any and end label
TEST(ParserA603, ForkNamedJoinAnyWithEndLabel) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork : f1\n"
                 "      #10 a = 1;\n"
                 "    join_any : f1\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
  EXPECT_EQ(stmt->label, "f1");
}

// §9.3.4: Named fork with join_none and end label
TEST(ParserA603, ForkNamedJoinNoneWithEndLabel) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork : f2\n"
                 "      #10 a = 1;\n"
                 "    join_none : f2\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(stmt->label, "f2");
}

// §9.3.2: Fork with block_item_declaration (variable in fork scope)
TEST(ParserA603, ForkWithVarDecl) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      automatic int k = 5;\n"
                 "      #10 a = k;\n"
                 "    join_none\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->fork_stmts[0]->var_is_automatic);
}

// §9.3.2: Fork with multiple concurrent statements
TEST(ParserA603, ForkMultipleStmts) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      a = 1;\n"
                 "      b = 2;\n"
                 "      c = 3;\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->fork_stmts.size(), 3u);
}

// §9.3.2: Fork with begin...end sub-blocks (each is one concurrent process)
TEST(ParserA603, ForkWithBeginEndSubBlocks) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      begin\n"
                 "        a = 1;\n"
                 "        b = 2;\n"
                 "      end\n"
                 "      begin\n"
                 "        c = 3;\n"
                 "        d = 4;\n"
                 "      end\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kBlock);
}

// §9.3.3: Nested fork inside begin-end
TEST(ParserA603, NestedForkInSeqBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      begin\n"
                 "        fork\n"
                 "          a = 1;\n"
                 "        join\n"
                 "      end\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->fork_stmts.size(), 1u);
  auto *inner_block = stmt->fork_stmts[0];
  EXPECT_EQ(inner_block->kind, StmtKind::kBlock);
  EXPECT_EQ(inner_block->stmts[0]->kind, StmtKind::kFork);
}

// §9.3.5: Statement label on begin-end block
TEST(ParserA603, SeqBlockWithStatementLabel) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    labelA: begin\n"
                 "      a = 1;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->label, "labelA");
}

// §9.3.5: Statement label on fork-join block
TEST(ParserA603, ForkWithStatementLabel) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    labelB: fork\n"
                 "      a = 1;\n"
                 "    join_none : labelB\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "labelB");
}

// ---------------------------------------------------------------------------
// action_block: statement_or_null | [statement] else statement_or_null
// ---------------------------------------------------------------------------

// §16.3: action_block in immediate assert — pass statement only
TEST(ParserA603, ActionBlockAssertPassOnly) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    assert (a) $display(\"pass\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// §16.3: action_block in immediate assert — pass and else (fail) statement
TEST(ParserA603, ActionBlockAssertPassAndFail) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    assert (a) $display(\"pass\"); else $display(\"fail\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// §16.3: action_block with null pass (semicolon), else fail
TEST(ParserA603, ActionBlockAssertNullPassElseFail) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    assert (a) else $error(\"fail\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// §16.3: action_block with null statement (just semicolon, no actions)
TEST(ParserA603, ActionBlockAssertNullStmt) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    assert (a);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
}

// §16.3: action_block in assume statement
TEST(ParserA603, ActionBlockAssume) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    assume (x) $display(\"ok\"); else $error(\"bad\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// §15.5.4: action_block in wait_order statement
TEST(ParserA603, ActionBlockWaitOrder) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order (a, b, c) $display(\"ok\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
}

// §15.5.4: action_block in wait_order with else clause
TEST(ParserA603, ActionBlockWaitOrderElse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order (a, b) else $display(\"out of order\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
}
