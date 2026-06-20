#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParallelBlockParsing, ForkJoinAnyKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
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

TEST(ParallelBlockParsing, ForkJoinNoneKeyword) {
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

TEST(ParallelBlockParsing, ForkWithForLoop) {
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

TEST(ParallelBlockParsing, ForkJoinInProgramBlock) {
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

TEST(ParallelBlockParsing, ForkThreadWithDelayedAssign) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);

  for (size_t i = 0; i < 2; ++i) {
    auto* thread = stmt->fork_stmts[i];
    EXPECT_EQ(thread->kind, StmtKind::kBlock);
    EXPECT_EQ(thread->stmts.size(), 3u);
  }
}

TEST(ParallelBlockParsing, ForkJoinTwoDelayedStmts) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kDelay);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kDelay);
}

TEST(ParallelBlockParsing, ForkDelayControlsInThreads) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);

  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_GE(stmt->fork_stmts[0]->stmts.size(), 2u);
}

TEST(ParallelBlockParsing, ForkEventControlsInThreads) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kEventControl);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kEventControl);
}

}  // namespace
