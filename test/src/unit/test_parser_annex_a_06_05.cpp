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

TEST(TimingControlSyntaxParsing, DelayControlNumeric) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
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

TEST(TimingControlSyntaxParsing, DelayControlParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #(10) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
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

TEST(TimingControlSyntaxParsing, EventControlPosedge) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->body, nullptr);
}

TEST(TimingControlSyntaxParsing, EventControlNegedge) {
  auto r = Parse(
      "module m;\n"
      "  always @(negedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(TimingControlSyntaxParsing, EventControlBareIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @r x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_NE(stmt->events[0].signal, nullptr);
}

TEST(TimingControlSyntaxParsing, EventControlParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(clk) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
}

TEST(TimingControlSyntaxParsing, EdgeIdentifiers) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge a or negedge b or edge c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 3u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kEdge);
}

TEST(TimingControlSyntaxParsing, ClockingEventPosedge) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(TimingControlSyntaxParsing, ClockingEventNegedge) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(negedge clk) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
}

TEST(TimingControlSyntaxParsing, EventExprEdge) {
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
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kEdge);
}

TEST(TimingControlSyntaxParsing, EventExprAnyChange) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
}

TEST(TimingControlSyntaxParsing, IntraAssignDelayBlocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = #5 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(TimingControlSyntaxParsing, IntraAssignEventBlocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(TimingControlSyntaxParsing, IntraAssignRepeatEventBlocking) {
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
  EXPECT_FALSE(stmt->events.empty());
}

TEST(TimingControlSyntaxParsing, IntraAssignDelayNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= #5 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(TimingControlSyntaxParsing, IntraAssignEventNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_FALSE(stmt->events.empty());
}

TEST(TimingControlSyntaxParsing, IntraAssignRepeatEventNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= repeat(5) @(posedge clk) data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

TEST(TimingControlSyntaxParsing, RepeatEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= repeat(3) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
}

TEST(TimingControlSyntaxParsing, WaitStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait(done) $display(\"done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(TimingControlSyntaxParsing, WaitConditionStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (ready) x = 1;\n"
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

TEST(TimingControlSyntaxParsing, WaitConditionNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (ready) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

TEST(TimingControlSyntaxParsing, WaitFork) {
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

TEST(TimingControlSyntaxParsing, WaitMissingLParen) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial wait ready a = 1;\n"
      "endmodule\n").has_errors);
}

TEST(TimingControlSyntaxParsing, WaitMissingRParen) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial wait(ready a = 1;\n"
      "endmodule\n").has_errors);
}

TEST(TimingControlSyntaxParsing, WaitForkMissingSemicolon) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait fork\n"
      "  end\n"
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

TEST(TimingControlSyntaxParsing, IntraAssignRepeatEventMissingAt) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= repeat(3) (posedge clk) b;\n"
      "  end\n"
      "endmodule\n").has_errors);
}

TEST(TimingControlSyntaxParsing, EventControlHierarchicalSignal) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge top.u1.clk) x = 1;\n"
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

TEST(TimingControlSyntaxParsing, WaitWithBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait(done) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(TimingControlSyntaxParsing, IntraAssignDelayParenBlocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = #(1:2:3) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(TimingControlSyntaxParsing, IntraAssignRepeatEventMultipleEvents) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= repeat(2) @(posedge clk or negedge rst) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_GE(stmt->events.size(), 2u);
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
