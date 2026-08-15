#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(BlockNameParsing, MismatchedEndLabelBeginEndErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk_a\n"
      "    $display(\"hello\");\n"
      "  end : blk_b\n"
      "endmodule\n");
  // §9.3.4 owns the end-label rule; A.6.3 only states the block productions.
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'blk_b' does not match block name 'blk_a'", 4,
      "9.3.4"));
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
  // §9.3.4 owns the end-label rule; A.6.3 only states the block productions.
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'blk_b' does not match block name 'blk_a'", 5,
      "9.3.4"));
}

TEST(BlockNameParsing, EndLabelWithoutStartLabelErrors) {
  // §9.3.4 (printed p.229): "It shall be an error if the name at the end is
  // different from the block name at the beginning." A block with no name at
  // begin but a name after end has a name "different from" (none at) the
  // beginning, so an end label without a matching start label is illegal.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end : unnamed_end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'unnamed_end' specified for unnamed block", 4,
      "9.3.4"));
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
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "endmodule\n");
  // The seq_block body runs until `end`, so `endmodule` is taken as a statement
  // and reaches ParsePrimaryExpr, whose report is filed under §11.2.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 4, "11.2"));
}

TEST(BlockStatementSyntaxParsing, UnterminatedParBlockErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "  end\n"
      "endmodule\n");
  // §9.3.2 owns the join_keyword production, and Parser::ParseForkStmt demands
  // it at the `end` on line 5, where its statement loop stops. That `end`
  // closes the seq_block of §9.3.1 on line 2, so the fork reports it and leaves
  // it rather than taking it for a statement.
  EXPECT_TRUE(ReportedError(
      r.diags, "expected join, join_any or join_none to close the parallel", 5,
      "9.3.2"));
}

TEST(BlockStatementSyntaxParsing, BeginWithJoinTerminatorErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "  join\n"
      "endmodule\n");
  // A seq_block ends only at `end`, so `join` is taken as a statement and
  // reaches ParsePrimaryExpr, whose report is filed under §11.2.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 4, "11.2"));
}

TEST(BlockStatementSyntaxParsing, ForkWithEndTerminatorErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  // The `end` on line 5 goes to the seq_block that opened on line 2, which is
  // what leaves the `end` on line 6 with no block left to close. §23.2.4 owns
  // the module body, so Parser::ParseTypedItemOrInst reports that second `end`
  // there. This case claims that recovery; the §9.3.2 report this source also
  // draws is named by BlockStatementSyntaxParsing.ParBlockMissingJoinRejected
  // in test/src/unit/test_parser_annex_a_06_03.cpp.
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 6, "23.2.4"));
}

}  // namespace
