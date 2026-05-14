#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingControlSyntaxParsing, DelayControlHash) {
  auto r = Parse(
      "module m;\n"
      "  initial #10 a = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(TimingControlSyntaxParsing, DelayControlParenExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial #(5 + 3) a = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(TimingControlSyntaxParsing, DelayControlIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #d x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_EQ(stmt->delay->kind, ExprKind::kIdentifier);
}

TEST(TimingControlSyntaxParsing, DelayControlMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #(1:2:3) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_EQ(stmt->delay->kind, ExprKind::kMinTypMax);
}

// posedge / negedge event-control AST encoding is governed by §9.4.2;
// canonical coverage lives in test_parser_clause_09_04_02.cpp.

TEST(TimingControlSyntaxParsing, EventControlStar) {
  auto r = Parse(
      "module m;\n"
      "  always @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TimingControlSyntaxParsing, EventControlStarParen) {
  auto r = Parse(
      "module m;\n"
      "  always @(*) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TimingControlSyntaxParsing, EventControlAtStar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @* y = a & b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
}

TEST(TimingControlSyntaxParsing, EventControlAtStarParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(*) y = a & b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
}

// `@id` (§15.5.2 named-event wait) and `@(any-signal)` (§9.4.2 any-change)
// AST encoding are tested in test_parser_clause_15_05_02.cpp and
// test_parser_clause_09_04_02.cpp respectively.

// posedge / negedge / edge / any-change AST-encoding tests for the
// event-control form belong to §9.4.2 and live in
// test_parser_clause_09_04_02.cpp. The multi-edge `or` / `,` combinations
// belong to §9.4.2.1 and live in test_parser_clause_09_04_02_01.cpp.

TEST(TimingControlSyntaxParsing, WaitOrder) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) $display(\"ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_GE(stmt->wait_order_events.size(), 3u);
}

// --- Error conditions and edge cases ---

TEST(TimingControlSyntaxParsing, DelayControlMissingRParen) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial #(5 + 3 a = 1;\n"
      "endmodule\n").has_errors);
}

TEST(TimingControlSyntaxParsing, EventControlMissingRParen) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial @(posedge clk a = 1;\n"
      "endmodule\n").has_errors);
}

TEST(TimingControlSyntaxParsing, WaitOrderMissingLParen) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial wait_order a, b;\n"
      "endmodule\n").has_errors);
}

TEST(TimingControlSyntaxParsing, WaitOrderMissingRParen) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial wait_order(a, b ;\n"
      "endmodule\n").has_errors);
}

TEST(TimingControlSyntaxParsing, CycleDelayStmtParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##(3) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCycleDelay);
  EXPECT_NE(stmt->cycle_delay, nullptr);
}

TEST(TimingControlSyntaxParsing, CycleDelayStmtLiteral) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##5 ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCycleDelay);
  EXPECT_NE(stmt->cycle_delay, nullptr);
}

TEST(TimingControlSyntaxParsing, CycleDelayMissingSemicolon) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##5\n"
      "  end\n"
      "endmodule\n").has_errors);
}

TEST(TimingControlSyntaxParsing, CycleDelayMissingRParen) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##(5 ;\n"
      "  end\n"
      "endmodule\n").has_errors);
}

TEST(TimingControlSyntaxParsing, IntraAssignCycleDelayBlocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = ##3 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->cycle_delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(TimingControlSyntaxParsing, IntraAssignCycleDelayNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= ##3 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->cycle_delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

// `@(posedge top.u1.clk)` moved to test_parser_clause_09_04_02.cpp as
// EventControlHierarchicalSignal — §9.4.2 owns the posedge rule.

TEST(TimingControlSyntaxParsing, WaitOrderWithActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) $display(\"ok\");\n"
      "    else $display(\"fail\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TimingControlSyntaxParsing, WaitOrderElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b) else $display(\"out of order\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->then_branch, nullptr);
}

TEST(TimingControlSyntaxParsing, WaitOrderNullAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
}

TEST(TimingControlSyntaxParsing, WaitOrderSingleEvent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(ev) $display(\"ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_GE(stmt->wait_order_events.size(), 1u);
}

TEST(TimingControlSyntaxParsing, DelayControlZero) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #0 x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(TimingControlSyntaxParsing, DelayControlRealLiteral) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #1.5 x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

// --- delay_or_event_control ::= repeat ( expression ) event_control ---
//
// The repeat form attaches to the RHS of an assignment as intra-assignment
// timing: `lhs = repeat (N) @(event_control) rhs;` (§A.6.5 / §10.4.2).

TEST(TimingControlSyntaxParsing, RepeatEventControlInAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = repeat(3) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(TimingControlSyntaxParsing, RepeatEventControlNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= repeat(5) @(negedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
}

// --- jump_statement ::= return [ expression ] ; | break ; | continue ; ---

TEST(JumpStatementSyntaxParsing, BreakStatementBnf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    break;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBreak);
}

TEST(JumpStatementSyntaxParsing, ContinueStatementBnf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    continue;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kContinue);
}

TEST(JumpStatementSyntaxParsing, ReturnStatementBnf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    return;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
  EXPECT_EQ(stmt->expr, nullptr);
}

TEST(JumpStatementSyntaxParsing, ReturnWithExpressionBnf) {
  auto r = Parse(
      "module m;\n"
      "  function int f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ret = FindReturnStmt(r);
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(ret->kind, StmtKind::kReturn);
  EXPECT_NE(ret->expr, nullptr);
}

TEST(JumpStatementSyntaxParsing, ReturnMissingSemicolonBnf) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  function int f();\n"
      "    return 42\n"
      "  endfunction\n"
      "endmodule\n").has_errors);
}

TEST(JumpStatementSyntaxParsing, BreakMissingSemicolonBnf) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial forever begin break end\n"
      "endmodule\n").has_errors);
}

TEST(JumpStatementSyntaxParsing, ContinueMissingSemicolonBnf) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial forever begin continue end\n"
      "endmodule\n").has_errors);
}

// --- wait_statement ::= wait ( expression ) statement_or_null
//                      | wait fork ;
//                      | wait_order ( ... ) action_block ---
// (wait_order tests above; here we cover the bare wait and wait fork forms.)

TEST(WaitStatementSyntaxParsing, WaitExpressionStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (done) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(WaitStatementSyntaxParsing, WaitExpressionNullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (done) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(WaitStatementSyntaxParsing, WaitForkStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitFork);
}

TEST(WaitStatementSyntaxParsing, WaitMissingLParenErrors) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait done) a = 1;\n"
      "  end\n"
      "endmodule\n").has_errors);
}

TEST(WaitStatementSyntaxParsing, WaitForkMissingSemicolonErrors) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait fork\n"
      "  end\n"
      "endmodule\n").has_errors);
}

// --- Parenthesized event_expression (§A.6.5) ---

TEST(TimingControlSyntaxParsing, ParenthesizedEventExprEdges) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @((posedge clk or negedge rst)) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
}

TEST(TimingControlSyntaxParsing, ParenthesizedEventExprNested) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(((posedge clk))) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

}  // namespace
