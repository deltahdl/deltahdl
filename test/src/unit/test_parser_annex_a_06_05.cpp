#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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

TEST(TimingControlSyntaxParsing, DelayControlMissingRParen) {
  auto r = Parse(
      "module m;\n"
      "  initial #(5 + 3 a = 1;\n"
      "endmodule\n");
  // §9.4.1 owns the delay_control parenthesis; A.6.5 only states its BNF.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got identifier", 2, "9.4.1"));
}

TEST(TimingControlSyntaxParsing, EventControlMissingRParen) {
  auto r = Parse(
      "module m;\n"
      "  initial @(posedge clk a = 1;\n"
      "endmodule\n");
  // §9.4.2 owns the event_control parenthesis; A.6.5 only states its BNF.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got identifier", 2, "9.4.2"));
}

TEST(TimingControlSyntaxParsing, WaitOrderMissingLParen) {
  auto r = Parse(
      "module m;\n"
      "  initial wait_order a, b;\n"
      "endmodule\n");
  // §15.5.4 owns wait_order; A.6.5 only states its BNF.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 2, "15.5.4"));
}

TEST(TimingControlSyntaxParsing, WaitOrderMissingRParen) {
  auto r = Parse(
      "module m;\n"
      "  initial wait_order(a, b ;\n"
      "endmodule\n");
  // §15.5.4 owns wait_order; A.6.5 only states its BNF.
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 2, "15.5.4"));
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
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##5\n"
      "  end\n"
      "endmodule\n");
  // A cycle_delay takes a statement_or_null after it, so `end` is taken as the
  // statement and reaches ParsePrimaryExpr, whose report is filed under §11.2.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 4, "11.2"));
}

TEST(TimingControlSyntaxParsing, CycleDelayMissingRParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##(5 ;\n"
      "  end\n"
      "endmodule\n");
  // §14.11 owns the cycle_delay parenthesis; A.6.5 only states its BNF.
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 3, "14.11"));
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

// The `[ expression ]` alternative of the A.6.5 jump_statement
// production. The clause 12.8 rule that a value-returning function must
// supply that expression is covered by
// JumpStatementSyntaxParsing.ReturnValueFromNonVoidFunction in
// test_parser_subclause_12_08.cpp.
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
  auto r = Parse(
      "module m;\n"
      "  function int f();\n"
      "    return 42\n"
      "  endfunction\n"
      "endmodule\n");
  // §12.8 owns the jump statements; A.6.5 only states their BNF. `endfunction`
  // stands where the ';' was wanted.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endfunction'", 4, "12.8"));
}

TEST(JumpStatementSyntaxParsing, BreakMissingSemicolonBnf) {
  auto r = Parse(
      "module m;\n"
      "  initial forever begin break end\n"
      "endmodule\n");
  // §12.8 owns the jump statements; A.6.5 only states their BNF.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'end'", 2, "12.8"));
}

TEST(JumpStatementSyntaxParsing, ContinueMissingSemicolonBnf) {
  auto r = Parse(
      "module m;\n"
      "  initial forever begin continue end\n"
      "endmodule\n");
  // §12.8 owns the jump statements; A.6.5 only states their BNF.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'end'", 2, "12.8"));
}

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
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait done) a = 1;\n"
      "  end\n"
      "endmodule\n");
  // §9.4.3 owns the wait condition parenthesis; A.6.5 only states its BNF.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 3, "9.4.3"));
}

TEST(WaitStatementSyntaxParsing, WaitForkMissingSemicolonErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait fork\n"
      "  end\n"
      "endmodule\n");
  // §9.6.1 owns wait fork; A.6.5 only states its BNF. `end` stands where the
  // ';' was wanted.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'end'", 4, "9.6.1"));
}

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

// event_trigger ::= ->> [ delay_or_event_control ]
// hierarchical_event_identifier ; delay_or_event_control covers delay_control |
// event_control | repeat ( expression ) event_control.
TEST(EventTriggerSyntaxParsing, NonblockingWithEventControlClockingEvent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> @(posedge clk) ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(EventTriggerSyntaxParsing, NonblockingWithEventControlStar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> @* ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_TRUE(stmt->is_star_event);
}

TEST(EventTriggerSyntaxParsing, NonblockingWithRepeatEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> repeat (3) @(posedge clk) ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(EventTriggerSyntaxParsing, NonblockingRepeatEventControlMissingAt) {
  auto r = Parse(
      "module m;\n"
      "  initial ->> repeat (3) ev;\n"
      "endmodule\n");
  // §15.5.1 owns the ->> event trigger; A.6.5 only states its BNF. The repeat
  // form of an event control demands the '@' this source leaves out.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '@', got identifier", 2, "15.5.1"));
}

// event_trigger ::= ->> [ delay_or_event_control ] ...
// delay_or_event_control admits a delay_control (# delay_value) alternative,
// distinct from the event_control / repeat forms exercised above.
TEST(EventTriggerSyntaxParsing, NonblockingWithDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> #5 ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_TRUE(stmt->events.empty());
  EXPECT_NE(stmt->expr, nullptr);
}

// event_trigger ::= ->> [ delay_or_event_control ] ...
// The delay_or_event_control is optional; the bare ->> form omits it entirely.
TEST(EventTriggerSyntaxParsing, NonblockingWithoutDelayOrEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_EQ(stmt->delay, nullptr);
  EXPECT_TRUE(stmt->events.empty());
  EXPECT_FALSE(stmt->is_star_event);
  EXPECT_NE(stmt->expr, nullptr);
}

// event_trigger ::= -> hierarchical_event_identifier nonrange_select ;
TEST(EventTriggerSyntaxParsing, BlockingEventTrigger) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(EventTriggerSyntaxParsing, BlockingEventTriggerHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial -> top.evt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
}

// event_trigger ::= -> hierarchical_event_identifier nonrange_select ;
// The nonrange_select permits a bit/element select on the event identifier,
// e.g. triggering one element of an event array.
TEST(EventTriggerSyntaxParsing, BlockingEventTriggerWithSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> ev[1];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSelect);
}

// disable_statement ::= disable hierarchical_task_identifier ;
//                    |  disable hierarchical_block_identifier ;
//                    |  disable fork ;
TEST(DisableStatementSyntaxParsing, DisableHierarchicalIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable some_task;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(DisableStatementSyntaxParsing, DisableFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisableFork);
}

TEST(DisableStatementSyntaxParsing, DisableHierarchicalBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable m.blk;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

TEST(DisableStatementSyntaxParsing, DisableMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial disable foo\n"
      "endmodule\n");
  // §9.6.2 owns the disable statement; A.6.5 only states its BNF. `endmodule`
  // stands where the ';' was wanted.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "9.6.2"));
}

// event_expression ::= [ edge_identifier ] expression [ iff expression ]
TEST(TimingControlSyntaxParsing, EventExprWithIff) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk iff enable) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

TEST(TimingControlSyntaxParsing, EventExprPlainSignalIff) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(sig iff enable) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

// clocking_event ::= @ ps_identifier | @ hierarchical_identifier
TEST(TimingControlSyntaxParsing, EventControlBareIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @clk_event x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_NE(stmt->events[0].signal, nullptr);
}

// event_expression ::= event_expression or event_expression
//                   |  event_expression , event_expression
TEST(TimingControlSyntaxParsing, EventExprCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk, negedge rst) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
}

TEST(TimingControlSyntaxParsing, EventExprOrSeparated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk or negedge rst) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 2u);
}

// event_expression ::= [ edge_identifier ] expression [ iff expression ]
// The edge_identifier has three forms; posedge/negedge are exercised above,
// this covers the remaining `edge` (any-transition) form.
TEST(TimingControlSyntaxParsing, EventExprEdgeKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(edge clk) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kEdge);
}

// delay_or_event_control ::= repeat ( expression ) event_control
// observed via intra-assignment timing prefix (already covered for ->>
// above; here we observe the analogous form in an assignment statement).
// procedural_timing_control_statement ::= procedural_timing_control
//                                         statement_or_null
// where procedural_timing_control includes cycle_delay (## ...).
TEST(TimingControlSyntaxParsing, CycleDelayBeforeStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##2 x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCycleDelay);
  EXPECT_NE(stmt->body, nullptr);
}

// clocking_event ::= @ ps_identifier | @ hierarchical_identifier
//                  | @ ( event_expression )
TEST(TimingControlSyntaxParsing, EventControlHierarchicalIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @top.clk x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_NE(stmt->events[0].signal, nullptr);
}

// A.6.5 writes `wait_order ( hierarchical_identifier { ,
// hierarchical_identifier } ) action_block`, so an operand that is an
// expression rather than a name is outside the grammar. It parsed with no
// report because ParseWaitOrderStmt read each operand with ParseExpr, which
// accepts every expression Annex A writes.
//
// The other operand is a bare name that is legal, so the source differs from a
// legal one in the one operand the report has to be about.
TEST(TimingControlSyntaxParsing, WaitOrderOperandThatIsAnExpressionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a + b, c) ;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "wait_order operand shall be a hierarchical identifier", 3,
      "15.5.4"));
}

// The same rule reached by the operand the reading behind #3310 turned up. A
// function_subroutine_call is the one that reaches an elaborator walk over
// expressions: ForEachChildExpr hands Stmt::wait_order_events to every walker
// converted onto it, and the reason no case covers a call there is that A.6.5
// admits none.
TEST(TimingControlSyntaxParsing, WaitOrderOperandThatIsACallIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(f(x), c) ;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "wait_order operand shall be a hierarchical identifier", 3,
      "15.5.4"));
}

// A.6.5's operand is a hierarchical_identifier and not an identifier, and A.9.3
// writes one as `[ $root . ] { identifier constant_bit_select . } identifier`.
// A dotted name is therefore legal, and a check demanding a bare name would
// reject a source nothing reported before. The seven cases above all write bare
// identifiers, so none of them holds this shut.
TEST(TimingControlSyntaxParsing, WaitOrderOperandMayBeADottedName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(top.a, b) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
