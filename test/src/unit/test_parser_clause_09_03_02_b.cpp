#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParallelBlockParsing, AutoVarInForkBlock) {
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

  auto* branch0 = stmt->fork_stmts[0];
  ASSERT_EQ(branch0->kind, StmtKind::kBlock);
  ASSERT_GE(branch0->stmts.size(), 1u);
  EXPECT_EQ(branch0->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(branch0->stmts[0]->var_is_automatic);
}

TEST(ParallelBlockParsing, ForkInTaskBody) {
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

TEST(ParallelBlockParsing, ForkInAlwaysBlock) {
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

TEST(ParallelBlockParsing, ForkWithSystemCalls) {
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

TEST(ParallelBlockParsing, AutomaticTaskWithForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  task automatic parallel_work(input int a, input int b);\n"
      "    fork\n"
      "      $display(\"a=%0d\", a);\n"
      "      $display(\"b=%0d\", b);\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  auto* fork_stmt = item->func_body_stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_GE(fork_stmt->fork_stmts.size(), 2u);
}

TEST(ParallelBlockParsing, TypedefInForkJoin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    typedef int my_t;\n"
              "  join\n"
              "endmodule\n"));
}

TEST(ParallelBlockParsing, AutomaticVarInForkBlock) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 1u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->fork_stmts[0]->var_is_automatic);
}

TEST(ParallelBlockParsing, ForkAsDirectInitialBody) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->stmts.size(), 2u);
  EXPECT_EQ(stmt->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->stmts[1]->kind, StmtKind::kBlockingAssign);
}

TEST(ParallelBlockParsing, LocalparamInForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      localparam int N = 4;\n"
      "      a = N;\n"
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

TEST(ParallelBlockParsing, ParameterInForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      parameter int W = 8;\n"
      "      a = W;\n"
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

TEST(ParallelBlockParsing, LetDeclInForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      let inc(x) = x + 1;\n"
      "      a = inc(0);\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kLetDecl);
}

TEST(ParallelBlockParsing, ReturnInForkBody) {
  auto r = Parse(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      return;\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParallelBlockParsing, SingleStatementInFork) {
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
  EXPECT_EQ(stmt->fork_stmts.size(), 1u);
}

TEST(ParallelBlockParsing, EmptyForkJoinParses) {
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
  EXPECT_EQ(stmt->fork_stmts.size(), 0u);
}

TEST(ParallelBlockParsing, MultipleBlockItemDeclarationsBeforeStmts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      int x;\n"
      "      int y;\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 4u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->fork_stmts[2]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->fork_stmts[3]->kind, StmtKind::kBlockingAssign);
}

}  // namespace
