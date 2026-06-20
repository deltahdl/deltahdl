#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BlockStatementSyntaxParsing, SeqBlockBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 2u);
}

TEST(BlockStatementSyntaxParsing, SeqBlockWithLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : myblock\n"
      "    a = 1;\n"
      "  end : myblock\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "myblock");
}

TEST(BlockStatementSyntaxParsing, SeqBlockWithBlockItemDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(BlockStatementSyntaxParsing, ParBlockBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
}

TEST(BlockStatementSyntaxParsing, ParBlockJoinAny) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(BlockStatementSyntaxParsing, ParBlockJoinNone) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

TEST(BlockStatementSyntaxParsing, ParBlockWithLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : par_block\n"
      "      a = 1;\n"
      "    join : par_block\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "par_block");
}

TEST(BlockStatementSyntaxParsing, NestedSeqInPar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin a = 1; b = 2; end\n"
      "      begin c = 3; end\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kBlock);
}

TEST(BlockStatementSyntaxParsing, SeqBlockEmpty) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts.size(), 0u);
}

TEST(BlockStatementSyntaxParsing, SeqBlockWithVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(BlockStatementSyntaxParsing, SeqBlockWithParamDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    parameter int P = 42;\n"
      "    a = P;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_GE(body->stmts.size(), 2u);
}

TEST(BlockStatementSyntaxParsing, SingleStatementInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
}

TEST(BlockStatementSyntaxParsing, MultipleAssignmentsInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    c = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

TEST(BlockStatementSyntaxParsing, BlockWithOnlyVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a;\n"
      "    logic [3:0] b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
}

TEST(BlockStatementSyntaxParsing, MultipleSequentialBlocksInSameInitial) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin : first\n"
      "      a = 1;\n"
      "    end : first\n"
      "    begin : second\n"
      "      b = 2;\n"
      "    end : second\n"
      "    begin : third\n"
      "      c = 3;\n"
      "    end : third\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[0]->label, "first");
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->label, "second");
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[2]->label, "third");
}

TEST(BlockStatementSyntaxParsing, NamedNestedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : mid\n"
      "      begin : inner\n"
      "        x = 1;\n"
      "      end : inner\n"
      "    end : mid\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->label, "mid");
  ASSERT_EQ(body->stmts[0]->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->stmts[0]->label, "inner");
}

TEST(BlockStatementSyntaxParsing, BeginEndAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
}

TEST(BlockStatementSyntaxParsing, ForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork #10 a = 1; #20 b = 1; join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_EQ(stmt->fork_stmts.size(), 2u);
}

TEST(BlockStatementSyntaxParsing, ForkJoinAny) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork #10 a = 1; join_any\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(BlockStatementSyntaxParsing, ForkJoinNone) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork #10 a = 1; join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

TEST(BlockStatementSyntaxParsing, ForkJoinEmpty) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->fork_stmts.size(), 0u);
}

TEST(BlockStatementSyntaxParsing, ForkWithVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      automatic int k = 5;\n"
      "      #10 a = k;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->fork_stmts[0]->var_is_automatic);
}

TEST(BlockStatementSyntaxParsing, ForkMultipleStmts) {
  auto r = Parse(
      "module m;\n"
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->fork_stmts.size(), 3u);
}

TEST(BlockStatementSyntaxParsing, ForkWithBeginEndSubBlocks) {
  auto r = Parse(
      "module m;\n"
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kBlock);
}

TEST(BlockStatementSyntaxParsing, ForkWithIfElseThread) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kDelay);
}

TEST(BlockStatementSyntaxParsing, ForkJoinThreeThreads) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->fork_stmts.size(), 3u);
}

TEST(BlockStatementSyntaxParsing, ForkJoinAnyTwoThreads) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
  EXPECT_EQ(stmt->fork_stmts.size(), 2u);
}

TEST(BlockStatementSyntaxParsing, ForkJoinNoneSingleThread) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(stmt->fork_stmts.size(), 1u);
}

TEST(BlockStatementSyntaxParsing, ParallelBlockVarDeclInFork) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    int local_var;\n"
      "    begin local_var = 1; end\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 1u);
}

TEST(BlockStatementSyntaxParsing, ParallelBlockNestedBeginInFork) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    begin #10 a = 1; #20 a = 2; end\n"
      "    begin #15 b = 3; end\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kBlock);
}

TEST(BlockStatementSyntaxParsing, NamedForkJoinAny) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "race_threads");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(BlockStatementSyntaxParsing, ForkMixedStmtsAndBlocks) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 3u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kDelay);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[2]->kind, StmtKind::kDelay);
}

TEST(BlockStatementSyntaxParsing, VarDeclInFork) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(BlockStatementSyntaxParsing, BlockWithForkJoinInside) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "      #20 b = 2;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_GE(stmt->fork_stmts.size(), 2u);
}

TEST(BlockStatementSyntaxParsing, ForkWithBeginEndThreads) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[0]->stmts.size(), 2u);
}

TEST(BlockStatementSyntaxParsing, ForkJoinAsDirectBody) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoin);
}

TEST(BlockStatementSyntaxParsing, ForkJoinAnyAsDirectBody) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join_any\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinAny);
}

TEST(BlockStatementSyntaxParsing, ForkJoinNoneAsDirectBody) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join_none\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinNone);
}

TEST(BlockStatementSyntaxParsing, VarDeclInForkJoinAny) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    int x;\n"
              "    x = 1;\n"
              "  join_any\n"
              "endmodule\n"));
}

TEST(BlockStatementSyntaxParsing, VarDeclInForkJoinNone) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    int x;\n"
              "    x = 1;\n"
              "  join_none\n"
              "endmodule\n"));
}

TEST(BlockStatementSyntaxParsing, EmptyForkFollowedByStatement) {
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

TEST(BlockStatementSyntaxParsing, ForkWithNonblockingAssigns) {
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

TEST(BlockStatementSyntaxParsing, MultipleSequentialForks) {
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

TEST(BlockStatementSyntaxParsing, ForkJoinSingleBeginEnd) {
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

TEST(BlockStatementSyntaxParsing, VarDeclAndThreadInForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    int x;\n"
      "    x = 5;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  ASSERT_GE(body->fork_stmts.size(), 1u);
  EXPECT_EQ(body->fork_stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(BlockStatementSyntaxParsing, MultipleVarDeclsInFork) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 3u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kVarDecl);
}

TEST(BlockStatementSyntaxParsing, ForkJoinAsStatement) {
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

TEST(BlockStatementSyntaxParsing, SeqBlockNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

TEST(BlockStatementSyntaxParsing, ForkNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : my_fork\n"
      "      #10 a = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "my_fork");
}

}  // namespace
