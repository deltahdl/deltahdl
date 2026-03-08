#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

  auto* branch0 = stmt->fork_stmts[0];
  ASSERT_EQ(branch0->kind, StmtKind::kBlock);
  ASSERT_GE(branch0->stmts.size(), 1u);
  EXPECT_EQ(branch0->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(branch0->stmts[0]->var_is_automatic);
}

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

TEST(ParserSection4, Sec4_9_3_AutomaticTaskWithForkJoin) {
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

TEST(ParserA28, BlockItemInForkJoin) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 3u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kVarDecl);
}

TEST(ParserA28, TypedefInForkJoin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    typedef int my_t;\n"
              "  join\n"
              "endmodule\n"));
}

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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 1u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->fork_stmts[0]->var_is_automatic);
}

TEST(ParserSection10, Sec10_4_1_InForkJoinBlock) {
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

}
