#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult9f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9f Parse(const std::string& src) {
  ParseResult9f result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static Stmt* FirstInitialStmt(ParseResult9f& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt* NthInitialStmt(ParseResult9f& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

static Stmt* FirstAlwaysStmt(ParseResult9f& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kAlwaysBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt* FirstTaskStmt(ParseResult9f& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kTaskDecl) continue;
    if (item->func_body_stmts.empty()) return nullptr;
    return item->func_body_stmts[0];
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.4.5 -- Repeat event control (blocking)
// =============================================================================

// Blocking repeat event with posedge: a = repeat(3) @(posedge clk) b;
TEST(ParserSection9, Sec9_4_5_BlockingRepeatPosedge) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat event control (nonblocking)
// =============================================================================

// Nonblocking repeat event with posedge: a <= repeat(2) @(posedge clk) b;
TEST(ParserSection9, Sec9_4_5_NonblockingRepeatPosedge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a <= repeat(2) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

// =============================================================================
// LRM section 9.4.5 -- Repeat event with negedge
// =============================================================================

// Repeat event with negedge: a = repeat(4) @(negedge clk) b;
TEST(ParserSection9, Sec9_4_5_RepeatNegedge) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat event with bare signal (no edge specifier)
// =============================================================================

// Repeat event with bare signal: a = repeat(2) @(clk) b;
TEST(ParserSection9, Sec9_4_5_RepeatBareSignal) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat count is a variable
// =============================================================================

// Repeat count is a variable: a = repeat(n) @(posedge clk) b;
TEST(ParserSection9, Sec9_4_5_RepeatCountVariable) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat count is a constant expression
// =============================================================================

// Repeat count is a constant expression: a = repeat(2+1) @(posedge clk) b;
TEST(ParserSection9, Sec9_4_5_RepeatCountExpression) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat count of 1
// =============================================================================

// Repeat count of 1: a = repeat(1) @(posedge clk) b;
TEST(ParserSection9, Sec9_4_5_RepeatCountOne) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(1) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

// =============================================================================
// LRM section 9.4.5 -- Repeat count of 0 (edge case)
// =============================================================================

// Repeat count of 0: a = repeat(0) @(posedge clk) b;
TEST(ParserSection9, Sec9_4_5_RepeatCountZero) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(0) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
}

// =============================================================================
// LRM section 9.4.5 / 10.4.1 -- Intra-assignment delay (blocking)
// =============================================================================

// Blocking intra-assignment delay: a = #10 b;
TEST(ParserSection9, Sec9_4_5_BlockingIntraDelay) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial a = #10 b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

// =============================================================================
// LRM section 9.4.5 / 10.4.1 -- Intra-assignment delay (nonblocking)
// =============================================================================

// Nonblocking intra-assignment delay: a <= #5 b;
TEST(ParserSection9, Sec9_4_5_NonblockingIntraDelay) {
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

// =============================================================================
// LRM section 9.4.5 / 10.4.2 -- Intra-assignment event (blocking posedge)
// =============================================================================

// Blocking intra-assignment event: a = @(posedge clk) b;
TEST(ParserSection9, Sec9_4_5_BlockingIntraEventPosedge) {
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

// =============================================================================
// LRM section 9.4.5 / 10.4.2 -- Intra-assignment event (nonblocking negedge)
// =============================================================================

// Nonblocking intra-assignment event: a <= @(negedge clk) b;
TEST(ParserSection9, Sec9_4_5_NonblockingIntraEventNegedge) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat event with multiple events (or)
// =============================================================================

// Repeat event with multiple events: a = repeat(3) @(posedge clk or negedge
// rst) b;
TEST(ParserSection9, Sec9_4_5_RepeatMultipleEventsOr) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat event with multiple events (comma)
// =============================================================================

// Repeat event with comma-separated events: a = repeat(2) @(posedge clk,
// negedge rst) b;
TEST(ParserSection9, Sec9_4_5_RepeatMultipleEventsComma) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat event in always block
// =============================================================================

// Repeat event used inside an always block body.
TEST(ParserSection9, Sec9_4_5_RepeatInAlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  always @(posedge clk) begin\n"
      "    a <= repeat(2) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_FALSE(stmt->events.empty());
}

// =============================================================================
// LRM section 9.4.5 -- Repeat event in task
// =============================================================================

// Repeat event used in a task body.
TEST(ParserSection9, Sec9_4_5_RepeatInTask) {
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

// =============================================================================
// LRM section 9.4.5 -- Intra-assignment delay with expression
// =============================================================================

// Intra-assignment delay with parenthesized expression: a = #(x+y) b;
TEST(ParserSection9, Sec9_4_5_IntraDelayExpression) {
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

// =============================================================================
// LRM section 9.4.5 -- Intra-assignment with real delay
// =============================================================================

// Intra-assignment with real-valued delay: a = #3.5 b;
TEST(ParserSection9, Sec9_4_5_IntraDelayReal) {
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

// =============================================================================
// LRM section 9.4.5 -- Multiple intra-assignment statements in sequence
// =============================================================================

// Multiple intra-assignment statements in the same begin-end block.
TEST(ParserSection9, Sec9_4_5_MultipleIntraAssignSequence) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat event with concatenation RHS
// =============================================================================

// Repeat event control with concatenation on RHS.
TEST(ParserSection9, Sec9_4_5_RepeatConcatRhs) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat event with function call on RHS
// =============================================================================

// Repeat event control with system function call on RHS.
TEST(ParserSection9, Sec9_4_5_RepeatFuncCallRhs) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat event with edge keyword
// =============================================================================

// Repeat event with the 'edge' keyword: a = repeat(2) @(edge clk) b;
TEST(ParserSection9, Sec9_4_5_RepeatEdgeKeyword) {
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

// =============================================================================
// LRM section 9.4.5 -- Blocking assign with #0 delay
// =============================================================================

// Blocking assign with zero delay: a = #0 b;
TEST(ParserSection9, Sec9_4_5_BlockingIntraDelayZero) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial a = #0 b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

// =============================================================================
// LRM section 9.4.5 -- Nonblocking assign with #0 delay
// =============================================================================

// Nonblocking assign with zero delay: a <= #0 b;
TEST(ParserSection9, Sec9_4_5_NonblockingIntraDelayZero) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial a <= #0 b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

// =============================================================================
// LRM section 9.4.5 -- Repeat event with complex RHS expression
// =============================================================================

// Repeat event with a binary expression on the RHS.
TEST(ParserSection9, Sec9_4_5_RepeatComplexRhs) {
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

// =============================================================================
// LRM section 9.4.5 -- Intra-assignment event with multiple signals
// =============================================================================

// Intra-assignment event with multiple signals separated by 'or'.
TEST(ParserSection9, Sec9_4_5_IntraEventMultipleSignals) {
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

// =============================================================================
// LRM section 9.4.5 -- Repeat event in automatic task
// =============================================================================

// Repeat event inside an automatic task.
TEST(ParserSection9, Sec9_4_5_RepeatInAutoTask) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg clk, a, b;\n"
              "  task automatic sample;\n"
              "    a = repeat(4) @(posedge clk) b;\n"
              "  endtask\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 9.4.5 -- Repeat event signal field populated
// =============================================================================

// Verify the signal field of the event expression.
TEST(ParserSection9, Sec9_4_5_RepeatEventSignalField) {
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

// =============================================================================
// LRM section 9.4.5 -- ParseOk: repeat event parses without errors
// =============================================================================

// Validate ParseOk for a complete repeat event control scenario.
TEST(ParserSection9, Sec9_4_5_ParseOkRepeatEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg clk, a, b;\n"
              "  initial begin\n"
              "    a = repeat(10) @(posedge clk) b;\n"
              "    a <= repeat(5) @(negedge clk) b;\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 9.4.5 -- Intra-assignment delay no events field set
// =============================================================================

// Intra-assignment delay should not set the events field.
TEST(ParserSection9, Sec9_4_5_IntraDelayNoEventsField) {
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
