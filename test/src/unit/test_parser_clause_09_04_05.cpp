#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §9.4.5 intra-assignment timing controls — parser coverage. Syntax 9-6/9-4 are
// borrowed from Annex A, so these tests confirm the parser recognises each
// distinct intra-assignment form: delay (simple, parenthesised, expression,
// real), event control (posedge/negedge, blocking/nonblocking, OR lists), and
// the repeat event control (count forms, edge kinds, event lists, RHS forms).
// Redundant variants that parse identically have been removed.

TEST(IntraAssignTimingParsing, BlockingParenthesizedIntraDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = #(1:2:3) b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(IntraAssignTimingParsing, BlockingRepeatPosedge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(3) @(posedge clk) b;\n"
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

TEST(IntraAssignTimingParsing, RepeatNegedge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(4) @(negedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
}

TEST(IntraAssignTimingParsing, RepeatBareSignal) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(2) @(clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
}

TEST(IntraAssignTimingParsing, RepeatCountVariable) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  int n;\n"
      "  initial a = repeat(n) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingParsing, NonblockingRepeatEventFields) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, clk;\n"
      "  initial begin\n"
      "    q <= repeat(3) @(posedge clk) d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->text, "d");
}

TEST(IntraAssignTimingParsing, RepeatCountExpression) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(2+1) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_EQ(stmt->repeat_event_count->kind, ExprKind::kBinary);
}

TEST(IntraAssignTimingParsing, IntraAssignEventNegedge) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a = @(negedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingParsing, NonblockingIntraDelay) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial a <= #5 b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingParsing, BlockingIntraEventPosedge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->repeat_event_count, nullptr);
}

TEST(IntraAssignTimingParsing, NonblockingIntraEventNegedge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a <= @(negedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->repeat_event_count, nullptr);
}

TEST(IntraAssignTimingParsing, RepeatMultipleEventsOr) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, rst, a, b;\n"
      "  initial a = repeat(3) @(posedge clk or negedge rst) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
}

TEST(IntraAssignTimingParsing, RepeatMultipleEventsComma) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, rst, a, b;\n"
      "  initial a = repeat(2) @(posedge clk, negedge rst) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
}

static Stmt* FirstTaskStmt(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kTaskDecl) continue;
    if (item->func_body_stmts.empty()) return nullptr;
    return item->func_body_stmts[0];
  }
  return nullptr;
}

TEST(IntraAssignTimingParsing, RepeatInTask) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  task my_task;\n"
      "    a = repeat(5) @(posedge clk) b;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstTaskStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_FALSE(stmt->events.empty());
}

TEST(IntraAssignTimingParsing, IntraDelayExpression) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  int x, y;\n"
      "  initial a = #(x+y) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingParsing, IntraDelayReal) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial a = #3.5 b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(IntraAssignTimingParsing, MultipleIntraAssignSequence) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b, c, d;\n"
      "  initial begin\n"
      "    a = #10 b;\n"
      "    c <= @(posedge clk) d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(s0->delay, nullptr);
  EXPECT_EQ(s1->kind, StmtKind::kNonblockingAssign);
  ASSERT_FALSE(s1->events.empty());
}

TEST(IntraAssignTimingParsing, RepeatConcatRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg clk;\n"
      "  reg [7:0] a, b, c;\n"
      "  initial a = repeat(3) @(posedge clk) {b, c};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

TEST(IntraAssignTimingParsing, RepeatFuncCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg clk;\n"
      "  int a;\n"
      "  initial a = repeat(2) @(posedge clk) $random;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingParsing, RepeatEdgeKeyword) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(2) @(edge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kEdge);
}

TEST(IntraAssignTimingParsing, RepeatComplexRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg clk;\n"
      "  reg [7:0] a, b, c;\n"
      "  initial a = repeat(2) @(posedge clk) b + c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

TEST(IntraAssignTimingParsing, IntraEventMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, rst, a, b;\n"
      "  initial a = @(posedge clk or negedge rst) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->repeat_event_count, nullptr);
}

TEST(IntraAssignTimingParsing, IntraAssignEventPosedge) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, clk;\n"
      "  initial begin\n"
      "    q <= @(posedge clk) d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->text, "d");
}

TEST(IntraAssignTimingParsing, RepeatEventSignalField) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(2) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  ASSERT_NE(stmt->events[0].signal, nullptr);
  EXPECT_EQ(stmt->events[0].signal->text, "clk");
}

TEST(IntraAssignTimingParsing, IntraDelayNoEventsField) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial a = #10 b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_TRUE(stmt->events.empty());
  EXPECT_EQ(stmt->repeat_event_count, nullptr);
}

TEST(IntraAssignTimingParsing, IntraAssignRepeatEventMissingAt) {
  EXPECT_TRUE(Parse("module m;\n"
                    "  initial begin\n"
                    "    a <= repeat(3) (posedge clk) b;\n"
                    "  end\n"
                    "endmodule\n")
                  .has_errors);
}

}  // namespace
