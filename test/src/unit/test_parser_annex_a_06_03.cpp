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

TEST(BlockStatementSyntaxParsing, SeqBlockNamedWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blockB\n"
      "    a = 1;\n"
      "  end : blockB\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "blockB");
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

TEST(BlockStatementSyntaxParsing, ForkNamedWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : my_fork\n"
      "      #10 a = 1;\n"
      "    join : my_fork\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->label, "my_fork");
}

TEST(BlockStatementSyntaxParsing, ForkNamedJoinAnyWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : f1\n"
      "      #10 a = 1;\n"
      "    join_any : f1\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
  EXPECT_EQ(stmt->label, "f1");
}

TEST(BlockStatementSyntaxParsing, ForkNamedJoinNoneWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : f2\n"
      "      #10 a = 1;\n"
      "    join_none : f2\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(stmt->label, "f2");
}

TEST(BlockStatementSyntaxParsing, NamedForkJoinMatchingLabels) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "thread_group");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
}

TEST(BlockStatementSyntaxParsing, NamedForkJoinNone) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "bg_threads");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

TEST(BlockStatementSyntaxParsing, UnlabeledBlockHasEmptyLabel) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_TRUE(body->label.empty());
}

TEST(BlockStatementSyntaxParsing, AnonymousBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_TRUE(item->body->label.empty());
}

TEST(BlockStatementSyntaxParsing, NamedBeginEndNoEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk_no_end\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "blk_no_end");
}

TEST(BlockStatementSyntaxParsing, MultipleNamedBlocksSameLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin : block_a\n"
      "      int x;\n"
      "      x = 1;\n"
      "    end : block_a\n"
      "    begin : block_b\n"
      "      int y;\n"
      "      y = 2;\n"
      "    end : block_b\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->label, "block_a");
  EXPECT_EQ(body->stmts[1]->label, "block_b");
}

TEST(BlockStatementSyntaxParsing, ParallelBlockNamedForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : par_blk\n"
      "      #10 a = 1;\n"
      "      #20 b = 2;\n"
      "    join : par_blk\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "par_blk");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
}

TEST(BlockNameParsing, MatchingEndLabelBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : myblk\n"
      "    $display(\"hello\");\n"
      "  end : myblk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(BlockNameParsing, MismatchedEndLabelBeginEndErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk_a\n"
      "    $display(\"hello\");\n"
      "  end : blk_b\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BlockNameParsing, MatchingEndLabelForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : par_blk\n"
      "      $display(\"a\");\n"
      "    join : par_blk\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(BlockNameParsing, MismatchedEndLabelForkJoinErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : blk_a\n"
      "      $display(\"a\");\n"
      "    join : blk_b\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BlockNameParsing, EndLabelWithoutStartLabelOk) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end : unnamed_end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(BlockNameParsing, NamedBlockWithoutEndLabelOk) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : myblk\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(BlockStatementSyntaxParsing, SequentialBlockNamedWithDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    integer count;\n"
      "    count = 0;\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

TEST(BlockStatementSyntaxParsing, NamedSeqBlockTwoStatements) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : seq_blk\n"
      "    x = 1;\n"
      "    y = 2;\n"
      "  end : seq_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "seq_blk");
}

TEST(BlockStatementSyntaxParsing, SequentialBlockNamedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_seq\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end : my_seq\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->label, "my_seq");
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(BlockStatementSyntaxParsing, NamedBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    int x;\n"
      "    x = 1;\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->label, "my_block");
}

TEST(BlockStatementSyntaxParsing, NestedNamedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      int y;\n"
      "      y = 42;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->label, "outer");
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->label, "inner");
}

TEST(BlockStatementSyntaxParsing, NamedBeginEnd) {
  auto r = Parse(
      "module t;\n"
      "  initial begin : my_block\n"
      "    x = 1;\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

TEST(BlockStatementSyntaxParsing, NamedSeqBlockWithoutEndLabel) {
  auto r = Parse(
      "module t;\n"
      "  initial begin : blk\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "blk");
}

TEST(BlockStatementSyntaxParsing, NamedForkJoin) {
  auto r = Parse(
      "module t;\n"
      "  initial fork : my_fork\n"
      "    x = 1;\n"
      "  join : my_fork\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->label, "my_fork");
}

TEST(BlockStatementSyntaxParsing, NestedNamedSequentialBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      a = 1;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[0]->label, "inner");
}

TEST(BlockStatementSyntaxParsing, NamedForkJoinAnyDirectBody) {
  auto r = Parse(
      "module t;\n"
      "  initial fork : par_blk\n"
      "    x = 1;\n"
      "  join_any : par_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->label, "par_blk");
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinAny);
}

TEST(BlockStatementSyntaxParsing, NamedForkJoinBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : my_fork\n"
      "      $display(\"a\");\n"
      "      $display(\"b\");\n"
      "    join : my_fork\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto* fork_stmt = item->body->stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->label, "my_fork");
}

TEST(BlockStatementSyntaxParsing, NamedBeginEndMatchingLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : seq_block\n"
      "    a = 1;\n"
      "  end : seq_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "seq_block");
  EXPECT_EQ(body->stmts.size(), 1u);
}

TEST(BlockStatementSyntaxParsing, NamedBlockWithDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    parameter int N = 4;\n"
      "    int i;\n"
      "    for (i = 0; i < N; i++) begin\n"
      "    end\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "my_block");
}

TEST(BlockStatementSyntaxParsing, NestedNamedBlocksWithoutDecls) {
  auto r = Parse(
      "module t;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      x = 1;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->label, "inner");
}

TEST(BlockStatementSyntaxParsing, SeqBlockNullStatements) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ;\n"
      "    ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
}

TEST(BlockStatementSyntaxParsing, ParBlockNullStatements) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      ;\n"
      "      ;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
}

TEST(BlockStatementSyntaxParsing, UnterminatedSeqBlockErrors) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    a = 1;\n"
              "endmodule\n"));
}

TEST(BlockStatementSyntaxParsing, UnterminatedParBlockErrors) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    fork\n"
              "      a = 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(BlockStatementSyntaxParsing, BeginWithJoinTerminatorErrors) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    a = 1;\n"
              "  join\n"
              "endmodule\n"));
}

TEST(BlockStatementSyntaxParsing, ForkWithEndTerminatorErrors) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    fork\n"
              "      a = 1;\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
