// §9.6.2: Disable statement

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// disable_statement ::=
//   disable hierarchical_task_identifier ;
//   | disable hierarchical_block_identifier ;
//   | disable fork ;
// ---------------------------------------------------------------------------
// §9.6.2: disable named block
TEST(ParserA605, DisableBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    disable my_block;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}
// =============================================================================
// LRM section 9.3.1 -- Blocks with disable of named block.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockWithDisableOwnName) {
  auto r = Parse("module m;\n"
                 "  initial begin : my_blk\n"
                 "    a = 1;\n"
                 "    disable my_blk;\n"
                 "    b = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "my_blk");
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisable);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}
// ---------------------------------------------------------------------------
// 29. Named fork disabled by name
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_NamedForkDisabledByName) {
  auto r = Parse("module m;\n"
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
TEST(ParserSection9c, DisableLabeledBlock) {
  // LRM 9.6.2 example: block disables itself using its name.
  auto r = Parse("module m;\n"
                 "  initial begin : block_name\n"
                 "    a = b;\n"
                 "    disable block_name;\n"
                 "    c = a;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "block_name");
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisable);
}
// =============================================================================
// §9.6.2 -- Disable statement (additional tests)
// =============================================================================
TEST(ParserSection9, DisableNamedBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin : blk\n"
                 "    disable blk;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kDisable);
}
TEST(ParserSection9, DisableTaskName) {
  auto r = Parse("module m;\n"
                 "  task my_task;\n"
                 "  endtask\n"
                 "  initial begin\n"
                 "    disable my_task;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

// =============================================================================
// LRM section 9.6.2 -- Disable statement
// Disable named blocks and tasks from within and outside.
// =============================================================================
TEST(ParserSection9c, DisableBlockFromOutside) {
  // LRM 9.6.2 example 3: disable a named block from an always procedure.
  auto r = Parse("module m;\n"
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
  // The second initial block should contain a disable statement.
  auto *second_init = r.cu->modules[0]->items[1];
  ASSERT_NE(second_init, nullptr);
  ASSERT_NE(second_init->body, nullptr);
  ASSERT_GE(second_init->body->stmts.size(), 2u);
  EXPECT_EQ(second_init->body->stmts[1]->kind, StmtKind::kDisable);
}

TEST(ParserSection9c, DisableWithIfCondition) {
  // LRM 9.6.2 example 2: conditional disable as a forward goto.
  auto r = Parse("module m;\n"
                 "  initial begin : block_name\n"
                 "    a = 1;\n"
                 "    if (a == 0)\n"
                 "      disable block_name;\n"
                 "    b = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "block_name");
  ASSERT_GE(body->stmts.size(), 3u);
  // The if statement contains the disable.
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kIf);
}

TEST(ParserSection9c, DisableHierarchicalTaskName) {
  EXPECT_TRUE(ParseOk("module m;\n"
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

// §9.6.2: disable_statement
TEST(ParserA604, StmtItemDisableStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    disable my_block;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}
TEST(Parser, DisableStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    disable blk;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(ParserSection9, DisableIdentStillWorks) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    disable my_block;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}
// ---------------------------------------------------------------------------
// 30. Disable statement (task/block disable)
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_DisableStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin : blk\n"
                 "    disable blk;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

} // namespace
