#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

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
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got identifier", 2, "9.4.1"));
}

TEST(TimingControlSyntaxParsing, EventControlMissingRParen) {
  auto r = Parse(
      "module m;\n"
      "  initial @(posedge clk a = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got identifier", 2, "9.4.2"));
}

TEST(TimingControlSyntaxParsing, WaitOrderMissingLParen) {
  auto r = Parse(
      "module m;\n"
      "  initial wait_order a, b;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 2, "15.5.4"));
}

TEST(TimingControlSyntaxParsing, WaitOrderMissingRParen) {
  auto r = Parse(
      "module m;\n"
      "  initial wait_order(a, b ;\n"
      "endmodule\n");
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
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 4, "11.2"));
}

TEST(TimingControlSyntaxParsing, CycleDelayMissingRParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##(5 ;\n"
      "  end\n"
      "endmodule\n");
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
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endfunction'", 4, "12.8"));
}

TEST(JumpStatementSyntaxParsing, BreakMissingSemicolonBnf) {
  auto r = Parse(
      "module m;\n"
      "  initial forever begin break end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'end'", 2, "12.8"));
}

TEST(JumpStatementSyntaxParsing, ContinueMissingSemicolonBnf) {
  auto r = Parse(
      "module m;\n"
      "  initial forever begin continue end\n"
      "endmodule\n");
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
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '@', got identifier", 2, "15.5.1"));
}

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
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "9.6.2"));
}

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
