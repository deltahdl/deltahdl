// Tests for the head text of IEEE 1800-2023 §9.3 "Block statements" (the prose
// printed before §9.3.1). The head defines block statements as a means of
// grouping statements so that they act syntactically like a single statement,
// enumerates the two block kinds (sequential begin-end and parallel fork-join),
// and states the delimiter keywords for each. The per-kind characteristics,
// start/finish timing, naming, and labels belong to the descendant subclauses
// §9.3.1-§9.3.5 and are exercised by their own canonical files.
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §9.3 head: a sequential (begin-end) block acts syntactically like a single
// statement. Placing one in a single-statement position -- here the then-branch
// of an if with no additional wrapping -- yields exactly one statement node
// that nonetheless groups several inner statements.
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
  // The whole begin-end block fills the single then-branch slot.
  ASSERT_NE(body->then_branch, nullptr);
  EXPECT_EQ(body->then_branch->kind, StmtKind::kBlock);
  EXPECT_EQ(body->then_branch->stmts.size(), 2u);
}

// §9.3 head: a parallel (fork-join) block likewise acts as a single statement,
// so it too fits directly in the then-branch slot while grouping its members.
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

// §9.3 head: because a sequential block acts as a single statement, it also
// fills the single-statement body slot of a loop. Here a begin-end block is the
// body of a for loop and still groups its two inner statements.
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

// §9.3 head: a parallel block likewise acts as a single statement, so it fills
// the else-branch slot of an if with no extra wrapping.
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

// §9.3 head: the two block kinds are distinct constructs -- a begin-end block
// parses to a sequential block node, a fork-join block to a parallel one.
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

// §9.3 head: the sequential block is delimited by begin and end.
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

// §9.3 head negative: begin without a matching end is not a well-formed
// sequential block -- the missing delimiter is diagnosed.
TEST(BlockStatementParsing, SequentialMissingEndIsError) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "endmodule\n");
  // §9.3.1 owns the begin-end delimiter rule, so ParseBlockStmt files the
  // missing `end` under it; §9.3 has no report of its own. The block's
  // statement loop stops at `endmodule` without consuming it, so the report
  // stands on line 5 at the token at fault. It stood at the EOF on line 6 until
  // the loop was given the stop set, the block having swallowed the
  // `endmodule` looking for a statement.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endmodule'", 5, "9.3.1"));
}

// §9.3 head negative: a sequential block standing as a case item's statement is
// closed by `end` and not by `endcase`. §9.3.1 makes a seq_block a
// statement_or_null and §12.5's case_item takes one, so the block reaches
// Parser::ParseCaseStmt's item loop, and `endcase` is a distinct exit from the
// block's statement loop and a distinct token from `end`.
TEST(BlockStatementParsing, SequentialInACaseItemClosedByEndcaseNamesTheEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    case (x)\n"
      "      1: begin\n"
      "           a = 1;\n"
      "    endcase\n"
      "endmodule\n");
  // The block's statement loop stops at `endcase` without consuming it, so the
  // report stands on line 6 and Parser::ParseCaseStmt still finds the `endcase`
  // it expects under §12.5.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endcase'", 6, "9.3.1"));
}

// §9.3 head negative: the same source, with nothing else left unterminated, and
// the count is what this case adds. A block that swallowed the `endcase` drew
// the §11.2 "expected expression" report on it, the same on the `endmodule`
// behind it, its own §9.3.1 report at end of input rather than at the token at
// fault, and then left Parser::ParseCaseStmt to report the `endcase` missing
// under §12.5: four reports for one missing `end`.
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

// §9.3 head negative: a sequential block standing inside a parallel block is
// closed by `end` and not by the fork's join keyword. §9.3.2 gives
// `par_block ::= fork [ : block_identifier ] { block_item_declaration }
// { statement_or_null } join_keyword`, so a seq_block left open there is
// followed by a token that is not an `end` at all.
TEST(BlockStatementParsing, SequentialInsideAForkClosedByJoinNamesTheEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    begin\n"
      "      a = 1;\n"
      "  join\n"
      "endmodule\n");
  // The block's statement loop stops at `join` without consuming it, so the
  // report stands on line 5 and Parser::ParseForkStmt still finds the join
  // keyword it expects under §9.3.2.
  EXPECT_TRUE(ReportedError(r.diags, "expected 'end', got 'join'", 5, "9.3.1"));
}

// §9.3 head negative: a sequential block reaches a generate region through the
// initial block that holds it, Parser::ParseGenerateRegion reading module items
// and an initial block being one. A bare `begin` written straight into a
// generate region is a different production -- §27.3's generate_block, read by
// Parser::ParseGenerateBody -- so `initial` is what puts a seq_block there.
TEST(BlockStatementParsing,
     SequentialInAGenerateRegionClosedByEndgenerateNamesTheEnd) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    initial begin\n"
      "      a = 1;\n"
      "  endgenerate\n"
      "endmodule\n");
  // The block's statement loop stops at `endgenerate` without consuming it, so
  // the report stands on line 5 and Parser::ParseGenerateRegion still finds the
  // `endgenerate` it expects under §27.3.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endgenerate'", 5, "9.3.1"));
}

// §9.3 head: the parallel block is delimited by fork and one of join, join_any,
// or join_none. All three closing keywords are accepted as delimiters and the
// specific one is recorded.
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

// §9.3 head negative: a parallel block must be closed by one of the join
// keywords. A fork with no join/join_any/join_none delimiter is not a
// well-formed parallel block and is diagnosed.
TEST(BlockStatementParsing, ParallelMissingJoinIsError) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  initial fork\n"
      "    a = 1'b0;\n"
      "    b = 1'b1;\n"
      "endmodule\n");
  // §9.3.2 owns the fork-join delimiter rule, so Parser::ParseForkStmt files
  // the missing join keyword under it; §9.3 has no report of its own. The
  // fork's statement loop stops at `endmodule`, which closes an enclosing
  // construct, so the report stands on line 6.
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 6,
      "9.3.2"));
}

// §9.3 head negative: a parallel block is closed by a join keyword and not by
// the end of the file. A fork truncated at end of input is diagnosed under
// §9.3.2, the subclause whose join_keyword production the source never
// reached, rather than under whatever rule the enclosing module breaks next.
TEST(BlockStatementParsing,
     ParallelUnterminatedAtEndOfInputNamesTheJoinKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n");
  // The report stands at the EOF token, which Lexer::Advance places on line 4:
  // SkipWhitespaceAndComments crosses the newline that ends line 3 and
  // increments the line before MakeLoc reads it. The same source also draws the
  // module's own missing-`endmodule` report, and this case claims nothing about
  // that one.
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 4,
      "9.3.2"));
}

// §9.3 head negative: a fork standing in a task body is closed by a join
// keyword and not by `endtask`. §9.3.2 makes a par_block a statement_or_null,
// so a fork reaches Parser::ParseTaskDecl's body loop, and `endtask` is a
// distinct exit from the fork's statement loop and a distinct token from `end`.
TEST(BlockStatementParsing, ParallelInATaskClosedByEndtaskNamesTheJoinKeyword) {
  auto r = Parse(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      a = 1;\n"
      "  endtask\n"
      "endmodule\n");
  // The fork's statement loop stops at `endtask` without consuming it, so the
  // report stands on line 5 and the task's own body loop still finds the
  // `endtask` it expects under §13.3.
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 5,
      "9.3.2"));
}

// §9.3 head negative: a fork standing as a case item's statement is closed by a
// join keyword and not by `endcase`. §12.5's case_item takes a
// statement_or_null, so a fork reaches Parser::ParseCaseStmt's item loop, and
// `endcase` is a distinct exit from the fork's statement loop and a distinct
// token from `end`.
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
  // The fork's statement loop stops at `endcase` without consuming it, so the
  // report stands on line 6 and Parser::ParseCaseStmt still finds the `endcase`
  // it expects under §12.5.
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 6,
      "9.3.2"));
}

// §9.3 head negative: the same source, with nothing else left unterminated, and
// the count is what this case adds. A fork that swallowed the `endcase` drew
// the §11.2 "expected expression" report on it and then left
// Parser::ParseCaseStmt to report the `endcase` missing under §12.5, three
// reports for one missing join keyword.
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

// §9.3 head negative: a fork standing in a generate region is closed by a join
// keyword and not by `endgenerate`. Parser::ParseGenerateRegion reads module
// items and an initial block is one, so a fork reaches Parser::ParseForkStmt
// with `endgenerate` where the join keyword belongs.
TEST(BlockStatementParsing,
     ParallelInAGenerateRegionClosedByEndgenerateNamesTheJoinKeyword) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    initial fork\n"
      "      a = 1;\n"
      "  endgenerate\n"
      "endmodule\n");
  // The fork's statement loop stops at `endgenerate` without consuming it, so
  // the report stands on line 5 and Parser::ParseGenerateRegion still finds the
  // `endgenerate` it expects under §27.3.
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 5,
      "9.3.2"));
}

// §9.3 head negative: an unterminated parallel block leaves the token that
// closes the enclosing construct where it stands. The `end` on line 5 belongs
// to the sequential block of §9.3.1, so Parser::ParseForkStmt reports and does
// not consume it, Parser::ParseBlockStmt consumes it as its own, and the module
// closes on `endmodule`.
TEST(BlockStatementParsing,
     ParallelMissingJoinLeavesTheEnclosingEndToItsOwnProduction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "  end\n"
      "endmodule\n");
  // One report, and the count is the claim: a fork that swallowed the `end` and
  // the `endmodule` looking for a statement would draw the §11.2 "expected
  // expression" report on each of them and the §12.3 "expected ';'" beside, so
  // this fails on a §9.3.2 report bolted onto the old recovery.
  EXPECT_TRUE(ReportedError(
      r.diags,
      "expected join, join_any or join_none to close the parallel block", 5,
      "9.3.2"));
  EXPECT_EQ(r.diags.size(), 1u);
}

// §9.3 head negative: a token that is not one of join, join_any and join_none
// never becomes the block's terminator in the AST. Stmt::join_kind keeps the
// TokenKind::kKwJoin default declared in src/parser/ast_stmt.h, so ExecFork in
// src/simulator/stmt_exec.cpp and CheckRefArgsInForkBlocks in
// src/elaborator/elaborator_validate_funcbody.cpp read a join_keyword §9.3.2
// admits rather than the `end` that stopped the parse.
TEST(BlockStatementParsing, ParallelMalformedTerminatorDoesNotBecomeAJoinKind) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
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
