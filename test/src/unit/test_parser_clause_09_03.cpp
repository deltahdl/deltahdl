// Tests for the head text of IEEE 1800-2023 §9.3 "Block statements" (the prose
// printed before §9.3.1). The head defines block statements as a means of
// grouping statements so that they act syntactically like a single statement,
// enumerates the two block kinds (sequential begin-end and parallel fork-join),
// and states the delimiter keywords for each. The per-kind characteristics,
// start/finish timing, naming, and labels belong to the descendant subclauses
// §9.3.1-§9.3.5 and are exercised by their own canonical files.
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
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
