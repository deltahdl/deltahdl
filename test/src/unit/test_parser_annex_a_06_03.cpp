#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// -------------------------------------------------------------------------
// seq_block ::= begin [ : block_identifier ] { block_item_declaration }
//               { statement_or_null } end [ : block_identifier ]
// -------------------------------------------------------------------------

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

// Both block_identifiers present and matched (begin : name ... end : name).
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

// Leading block_identifier only; the optional trailing one is omitted.
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

// block_item_declaration (data_declaration) preceding the statements.
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

// block_item_declaration (parameter_declaration alternative).
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

// A seq_block is itself a statement_or_null, so it may nest within a block.
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

// -------------------------------------------------------------------------
// par_block ::= fork [ : block_identifier ] { block_item_declaration }
//               { statement_or_null } join_keyword [ : block_identifier ]
// join_keyword ::= join | join_any | join_none
// -------------------------------------------------------------------------

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

// Empty par_block: no block_item_declarations and no statements.
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

// Both block_identifiers present and matched (fork : name ... join : name).
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

// Leading block_identifier only; the optional trailing one is omitted.
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

// block_item_declaration (with automatic lifetime) inside a par_block.
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

// A seq_block composed as a statement_or_null thread inside a par_block.
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

// A par_block used directly as the initial statement (not wrapped in begin).
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

// -------------------------------------------------------------------------
// action_block ::= statement_or_null | [ statement ] else statement_or_null
// -------------------------------------------------------------------------

// First alternative: a bare pass statement (statement_or_null), no else clause.
TEST(BlockStatementSyntaxParsing, ActionBlockPassStatementOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (a) b = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// Second alternative in full: an optional pass statement followed by
// else and a fail statement_or_null.
TEST(BlockStatementSyntaxParsing, ActionBlockPassAndElseFail) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (a) b = 1; else c = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt->kind, StmtKind::kBlockingAssign);
}

// Second alternative with the leading statement omitted: else and a fail
// statement only, exercising the optional [ statement ] branch.
TEST(BlockStatementSyntaxParsing, ActionBlockElseOnlyOmittedPass) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (a) else c = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt->kind, StmtKind::kBlockingAssign);
}

// First alternative where statement_or_null is the null statement: the whole
// action block is just the terminating semicolon, so neither pass nor fail
// statement is produced.
TEST(BlockStatementSyntaxParsing, ActionBlockNullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// -------------------------------------------------------------------------
// Negative forms: the block productions mandate their closing keyword.
// -------------------------------------------------------------------------

// seq_block requires a closing end; reaching the module boundary without it
// is a parse error.
TEST(BlockStatementSyntaxParsing, SeqBlockMissingEndRejected) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    a = 1;\n"
              "endmodule\n"));
}

// par_block requires a join_keyword to close; terminating a fork with end
// is a parse error.
TEST(BlockStatementSyntaxParsing, ParBlockMissingJoinRejected) {
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
