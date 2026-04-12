#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BlockStartFinishParsing, SeqBlockNested) {
  auto r = Parse(
      "module m;\n"
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
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
}

TEST(BlockStartFinishParsing, NestedBeginEndTwoLevels) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    begin\n"
      "      b = 1;\n"
      "      c = 2;\n"
      "    end\n"
      "    d = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

TEST(BlockStartFinishParsing, DeeplyNestedBeginEndThreeLevels) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      begin\n"
      "        a = 1;\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 1u);
  auto* mid = body->stmts[0];
  EXPECT_EQ(mid->kind, StmtKind::kBlock);
  ASSERT_EQ(mid->stmts.size(), 1u);
  auto* inner = mid->stmts[0];
  EXPECT_EQ(inner->kind, StmtKind::kBlock);
  ASSERT_EQ(inner->stmts.size(), 1u);
  EXPECT_EQ(inner->stmts[0]->kind, StmtKind::kBlockingAssign);
}

TEST(BlockStartFinishParsing, NestedForkInSeqBlock) {
  auto r = Parse(
      "module m;\n"
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->fork_stmts.size(), 1u);
  auto* inner_block = stmt->fork_stmts[0];
  EXPECT_EQ(inner_block->kind, StmtKind::kBlock);
  EXPECT_EQ(inner_block->stmts[0]->kind, StmtKind::kFork);
}

TEST(BlockStartFinishParsing, ForkInBeginInFork) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 1u);
  auto* block = stmt->fork_stmts[0];
  EXPECT_EQ(block->kind, StmtKind::kBlock);
  ASSERT_GE(block->stmts.size(), 2u);
  EXPECT_EQ(block->stmts[1]->kind, StmtKind::kFork);
  EXPECT_EQ(block->stmts[1]->join_kind, TokenKind::kKwJoinNone);
}

TEST(BlockStartFinishParsing, NestedForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        fork\n"
      "          a = 1;\n"
      "          b = 2;\n"
      "        join\n"
      "      end\n"
      "      c = 3;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  auto* inner_block = stmt->fork_stmts[0];
  EXPECT_EQ(inner_block->kind, StmtKind::kBlock);
  ASSERT_GE(inner_block->stmts.size(), 1u);
  EXPECT_EQ(inner_block->stmts[0]->kind, StmtKind::kFork);
}

TEST(BlockStartFinishParsing, ForkInsideSeqBlockWithSurroundingStmts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    fork\n"
      "      b = 1;\n"
      "      c = 2;\n"
      "    join\n"
      "    d = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kFork);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

TEST(BlockStartFinishParsing, EmptyNestedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "    end\n"
      "    begin\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[0]->stmts.size(), 0u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->stmts.size(), 0u);
}

}  // namespace
