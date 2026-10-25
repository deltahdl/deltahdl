#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_stmt.h"

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

// A seq_block's declarations all come before its first statement, a null
// statement and a nested block among them, so a declaration after one is
// reported and one before it is not; a block is checked apart from the block
// it stands in.
TEST(BlockStatementSyntaxParsing,
     SeqBlockDeclarationAfterAStatementIsReported) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a;\n"
      "    a = 1;\n"
      "    int b;\n"
      "  end\n"
      "  initial begin : named\n"
      "    ;\n"
      "    parameter int P = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    begin\n"
      "      int c;\n"
      "    end\n"
      "    let l = 3;\n"
      "  end\n"
      "endmodule\n");
  const char* msg =
      "a declaration cannot follow a statement in a begin-end block";
  for (uint32_t line : {5U, 9U, 15U}) {
    EXPECT_TRUE(ReportedError(r.diags, msg, line, "9.3.1"));
  }
  for (uint32_t line : {3U, 13U}) {
    EXPECT_FALSE(ReportedError(r.diags, msg, line, "9.3.1"));
  }
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

// A par_block's declarations all come before its first statement, whichever
// join keyword closes it, so a declaration after one is reported and one
// before it is not.
TEST(BlockStatementSyntaxParsing,
     ParBlockDeclarationAfterAStatementIsReported) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    int a;\n"
      "    #1 a = 1;\n"
      "    int b;\n"
      "  join\n"
      "  initial fork : named\n"
      "    #1 $display(\"x\");\n"
      "    localparam int P = 2;\n"
      "  join_none\n"
      "endmodule\n");
  const char* msg =
      "a declaration cannot follow a statement in a fork-join block";
  for (uint32_t line : {5U, 9U}) {
    EXPECT_TRUE(ReportedError(r.diags, msg, line, "9.3.2"));
  }
  EXPECT_FALSE(ReportedError(r.diags, msg, 3, "9.3.2"));
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

// Second alternative with a null statement before the else: A.6.4 builds a
// statement from a statement_item, and no statement_item is a bare semicolon,
// so one written there with attribute instances before its semicolon is
// reported; a bare semicolon there is the first alternative, which ends the
// action block. Every construct that ends in an action_block
// reads it alike: an immediate and a deferred assertion, a concurrent
// assertion in procedural code, expect and wait_order. A null statement after
// the else, or one standing alone as the first alternative, draws no report.
TEST(BlockStatementSyntaxParsing, ActionBlockNullPassStatementBeforeElse) {
  auto r = Parse(
      "module m(input logic clk, a);\n"
      "  event e1, e2;\n"
      "  initial begin\n"
      "    assert (a) (* x *) ; else $error;\n"
      "    assume #0 (a) (* x *) ; else $error;\n"
      "    assert property (@(posedge clk) a) (* x *) ; else $error;\n"
      "    expect (@(posedge clk) a) (* x *) ; else $error;\n"
      "    wait_order (e1, e2) (* x *) ; else $error;\n"
      "    assert (a) else ;\n"
      "    assert (a) (* x *) ;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {4u, 5u, 6u, 7u, 8u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "an action block's statement before 'else' is a "
                              "statement, which cannot be null",
                              line, "A.6.3"));
  }
  EXPECT_EQ(r.diags.size(), 5u);
}

// -------------------------------------------------------------------------
// Negative forms: the block productions mandate their closing keyword.
// -------------------------------------------------------------------------

// seq_block requires a closing end; reaching the module boundary without it
// is a parse error.
TEST(BlockStatementSyntaxParsing, SeqBlockMissingEndRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "endmodule\n");
  // §9.3.1 owns seq_block, and Parser::ParseBlockStmt demands its `end` at the
  // `endmodule` that closes the construct the block stands in. It demanded it
  // at end-of-input on line 5 until the block's statement loop was given the
  // stop set, having swallowed the `endmodule` looking for a statement.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endmodule'", 4, "9.3.1"));
}

// par_block requires a join_keyword to close; terminating a fork with end
// is a parse error.
TEST(BlockStatementSyntaxParsing, ParBlockMissingJoinRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  // §9.3.2 owns par_block, and Parser::ParseForkStmt demands one of the three
  // join keywords at the `end` on line 5, which is where its statement loop
  // stops. The message names all three because join_keyword is a choice of
  // three, where TokenKindName would render one wanted keyword as `token`.
  EXPECT_TRUE(ReportedError(
      r.diags, "expected join, join_any or join_none to close the parallel", 5,
      "9.3.2"));
}

}  // namespace
