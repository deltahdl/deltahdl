#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DisableStatementParsing, DisableBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable my_block;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(DisableStatementParsing, BlockWithDisableOwnName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_blk\n"
      "    a = 1;\n"
      "    disable my_blk;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "my_blk");
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisable);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

TEST(DisableStatementParsing, NamedForkDisabledByName) {
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
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  auto* fork_stmt = body->stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->label, "my_fork");
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kDisable);
}
TEST(DisableStatementParsing, DisableNamedBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk\n"
      "    disable blk;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kDisable);
}
TEST(DisableStatementParsing, DisableTaskName) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "  endtask\n"
      "  initial begin\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

TEST(DisableStatementParsing, DisableBlockFromOutside) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    forever begin\n"
      "      @(posedge clk) x = x + 1;\n"
      "    end\n"
      "  end\n"
      "  initial begin\n"
      "    #100;\n"
      "    disable outer;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* second_init = r.cu->modules[0]->items[1];
  ASSERT_NE(second_init, nullptr);
  ASSERT_NE(second_init->body, nullptr);
  ASSERT_GE(second_init->body->stmts.size(), 2u);
  EXPECT_EQ(second_init->body->stmts[1]->kind, StmtKind::kDisable);
}

TEST(DisableStatementParsing, DisableWithIfCondition) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : block_name\n"
      "    a = 1;\n"
      "    if (a == 0)\n"
      "      disable block_name;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "block_name");
  ASSERT_GE(body->stmts.size(), 3u);

  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kIf);
}

TEST(DisableStatementParsing, DisableHierarchicalTaskName) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task;\n"
              "    begin\n"
              "      #100 x = 1;\n"
              "    end\n"
              "  endtask\n"
              "  initial begin\n"
              "    fork\n"
              "      my_task;\n"
              "    join_none\n"
              "    #50 disable my_task;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(DisableStatementParsing, DisableHierarchicalBlockPath) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable m.always1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(DisableStatementParsing, DisableInsideAlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  always begin : monostable\n"
      "    #250 q = 0;\n"
      "  end\n"
      "  always @(posedge clk) begin\n"
      "    disable monostable;\n"
      "    q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DisableStatementParsing, DisableNamedBlockWithinFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int f(input int x);\n"
              "    begin : blk\n"
              "      if (x == 0) disable blk;\n"
              "      return x;\n"
              "    end\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(DisableStatementParsing, DisableInsideForLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer_block\n"
      "    for (int i = 0; i < 10; i = i + 1) begin : inner_block\n"
      "      if (i == 5) disable inner_block;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DisableStatementParsing, DisableOuterBlockFromLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer_block\n"
      "    for (int i = 0; i < 10; i = i + 1) begin : inner_block\n"
      "      if (i == 5) disable outer_block;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DisableStatementParsing, MultipleDisablesInSequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable blk1;\n"
      "    disable blk2;\n"
      "    disable blk3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kDisable);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisable);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kDisable);
}

}  // namespace
