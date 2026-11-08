#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(BlockStatementParsing, SeqBlockActsAsSingleStatementInIfBranch) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  initial\n"
      "    if (1'b1)\n"
      "      begin\n"
      "        a = 1'b0;\n"
      "        b = 1'b1;\n"
      "      end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kIf);
  ASSERT_NE(body->then_branch, nullptr);
  EXPECT_EQ(body->then_branch->kind, StmtKind::kBlock);
  EXPECT_EQ(body->then_branch->stmts.size(), 2u);
}

TEST(BlockStatementParsing, ParBlockActsAsSingleStatementInIfBranch) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  initial\n"
      "    if (1'b1)\n"
      "      fork\n"
      "        a = 1'b0;\n"
      "        b = 1'b1;\n"
      "      join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kIf);
  ASSERT_NE(body->then_branch, nullptr);
  EXPECT_EQ(body->then_branch->kind, StmtKind::kFork);
  EXPECT_EQ(body->then_branch->fork_stmts.size(), 2u);
}

TEST(BlockStatementParsing, SeqBlockActsAsSingleStatementInForBody) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] s;\n"
      "  initial\n"
      "    for (int i = 0; i < 2; i = i + 1)\n"
      "      begin\n"
      "        s = s + 8'd1;\n"
      "        s = s + 8'd1;\n"
      "      end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kFor);
  ASSERT_NE(body->for_body, nullptr);
  EXPECT_EQ(body->for_body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->for_body->stmts.size(), 2u);
}

TEST(BlockStatementParsing, ParBlockActsAsSingleStatementInElseBranch) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  initial\n"
      "    if (1'b0)\n"
      "      a = 1'b1;\n"
      "    else\n"
      "      fork\n"
      "        a = 1'b0;\n"
      "        b = 1'b1;\n"
      "      join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kIf);
  ASSERT_NE(body->else_branch, nullptr);
  EXPECT_EQ(body->else_branch->kind, StmtKind::kFork);
  EXPECT_EQ(body->else_branch->fork_stmts.size(), 2u);
}

TEST(BlockStatementParsing, SequentialAndParallelAreDistinctKinds) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  initial begin\n"
      "    begin a = 1'b0; b = 1'b1; end\n"
      "    fork c = 1'b0; d = 1'b1; join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = InitialBody(r);
  ASSERT_NE(outer, nullptr);
  ASSERT_EQ(outer->kind, StmtKind::kBlock);
  ASSERT_EQ(outer->stmts.size(), 2u);
  EXPECT_EQ(outer->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(outer->stmts[1]->kind, StmtKind::kFork);
}

TEST(BlockStatementParsing, SequentialDelimitedByBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
}

TEST(BlockStatementParsing, SequentialMissingEndIsError) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endmodule'", 5, "9.3.1"));
}

TEST(BlockStatementParsing, SequentialInACaseItemClosedByEndcaseNamesTheEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    case (x)\n"
      "      1: begin\n"
      "           a = 1;\n"
      "    endcase\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endcase'", 6, "9.3.1"));
}

TEST(BlockStatementParsing,
     SequentialMissingEndLeavesTheEnclosingEndcaseToItsOwnProduction) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    case (x)\n"
      "      1: begin\n"
      "           a = 1;\n"
      "    endcase\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endcase'", 6, "9.3.1"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(BlockStatementParsing, SequentialInsideAForkClosedByJoinNamesTheEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    begin\n"
      "      a = 1;\n"
      "  join\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'end', got 'join'", 5, "9.3.1"));
}

TEST(BlockStatementParsing,
     SequentialInARandsequenceCodeBlockClosedByBraceNamesTheEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : {\n"
      "        begin\n"
      "          a = 1;\n"
      "      } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'end', got '}'", 7, "9.3.1"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(BlockStatementParsing,
     ParallelInARandsequenceCodeBlockClosedByBraceNamesTheJoinKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : {\n"
      "        fork\n"
      "          a = 1;\n"
      "      } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 7,
      "9.3.2"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(BlockStatementParsing,
     SequentialInAGenerateRegionClosedByEndgenerateNamesTheEnd) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    initial begin\n"
      "      a = 1;\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endgenerate'", 5, "9.3.1"));
}

TEST(BlockStatementParsing, ParallelDelimitedByForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  initial fork\n"
      "    a = 1'b0;\n"
      "    b = 1'b1;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoin);
}

TEST(BlockStatementParsing, ParallelDelimitedByForkJoinAny) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  initial fork\n"
      "    a = 1'b0;\n"
      "    b = 1'b1;\n"
      "  join_any\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinAny);
}

TEST(BlockStatementParsing, ParallelMissingJoinIsError) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  initial fork\n"
      "    a = 1'b0;\n"
      "    b = 1'b1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 6,
      "9.3.2"));
}

TEST(BlockStatementParsing,
     ParallelUnterminatedAtEndOfInputNamesTheJoinKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 4,
      "9.3.2"));
}

TEST(BlockStatementParsing, ParallelInATaskClosedByEndtaskNamesTheJoinKeyword) {
  auto r = Parse(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      a = 1;\n"
      "  endtask\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 5,
      "9.3.2"));
}

TEST(BlockStatementParsing,
     ParallelInACaseItemClosedByEndcaseNamesTheJoinKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    case (x)\n"
      "      1: fork\n"
      "           a = 1;\n"
      "    endcase\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 6,
      "9.3.2"));
}

TEST(BlockStatementParsing,
     ParallelMissingJoinLeavesTheEnclosingEndcaseToItsOwnProduction) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    case (x)\n"
      "      1: fork\n"
      "           a = 1;\n"
      "    endcase\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 6,
      "9.3.2"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(BlockStatementParsing,
     ParallelInAGenerateRegionClosedByEndgenerateNamesTheJoinKeyword) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    initial fork\n"
      "      a = 1;\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 5,
      "9.3.2"));
}

TEST(BlockStatementParsing,
     ParallelMissingJoinLeavesTheEnclosingEndToItsOwnProduction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 5,
      "9.3.2"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(BlockStatementParsing, ParallelMalformedTerminatorDoesNotBecomeAJoinKind) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 4,
      "9.3.2"));
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoin);
}

TEST(BlockStatementParsing, ParallelDelimitedByForkJoinNone) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  initial fork\n"
      "    a = 1'b0;\n"
      "    b = 1'b1;\n"
      "  join_none\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinNone);
}

}  // namespace
