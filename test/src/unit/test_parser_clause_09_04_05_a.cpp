// §9.4.5: Intra-assignment timing controls

#include "fixture_parser.h"

using namespace delta;

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

namespace {

// Intra-assignment delay: var = #delay expr.
TEST(ParserA223, IntraAssignmentDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg r;\n"
              "  initial r = #5 1'b1;\n"
              "endmodule"));
}

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

TEST(ParserA602, BlockingAssignment_WithIntraEvent) {
  // §10.4.2: blocking with intra-assignment event
  auto r = Parse(
      "module m;\n"
      "  initial begin a = @(posedge clk) b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->events.empty());
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, BlockingAssignment_WithRepeatEvent) {
  // §9.4.5: repeat(N) @(event) intra-assignment timing
  auto r = Parse(
      "module m;\n"
      "  initial begin a = repeat(3) @(posedge clk) b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

TEST(ParserA602, BlockingAssignment_ParenthesizedIntraDelay) {
  // Parenthesized intra-assignment delay with min:typ:max
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

TEST(ParserA602, NonblockingAssignment_WithRepeatEvent) {
  // Nonblocking with repeat(N) @(event) intra-assignment timing
  auto r = Parse(
      "module m;\n"
      "  initial begin q <= repeat(2) @(posedge clk) d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

struct ParseResult9c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9c Parse(const std::string& src) {
  ParseResult9c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult9c& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

TEST(ParserSection9, RepeatEventControlNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a <= repeat(2) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

struct ParseResult10d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10d Parse(const std::string& src) {
  ParseResult10d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult10d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// --- 2. Blocking assignment with intra-assignment delay: a = #10 b ---
TEST(ParserSection10, Sec10_4_1_IntraAssignDelay) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a = #10 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->delay, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "a");
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->text, "b");
}

// --- 3. Blocking assignment with intra-assignment event control ---
TEST(ParserSection10, Sec10_4_1_IntraAssignEvent) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

struct ParseResult9f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

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

struct ParseResult9g {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9g Parse(const std::string& src) {
  ParseResult9g result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
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

struct ParseResult11 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11 Parse(const std::string& src) {
  ParseResult11 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// --- 21. Nonblocking with repeat event control ---
TEST(ParserSection10, Sec10_4_2_RepeatEventControl) {
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

// --- 24. Nonblocking with negedge intra-assignment event ---
TEST(ParserSection10, Sec10_4_2_IntraAssignEventNegedge) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, clk;\n"
      "  initial begin\n"
      "    q <= @(negedge clk) d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  ASSERT_NE(stmt->rhs, nullptr);
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

static Stmt* FirstTaskStmt(ParseResult9f& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kTaskDecl) continue;
    if (item->func_body_stmts.empty()) return nullptr;
    return item->func_body_stmts[0];
  }
  return nullptr;
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

// --- 26. Blocking assignment with negedge intra-assignment event ---
TEST(ParserSection10, Sec10_4_1_IntraAssignNegedgeEvent) {
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

static Stmt* NthInitialStmt(ParseResult9f& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
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

struct ParseResult4b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static Stmt* FirstInitialStmt(ParseResult4b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 27. Non-blocking assign with intra-assignment delay (a <= #2 b)
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_NonblockingAssignWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a <= #2 b;\n"
      "  end\n"
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

// --- 3. Nonblocking with intra-assignment event: q <= @(posedge clk) d ---
TEST(ParserSection10, Sec10_4_2_IntraAssignEventPosedge) {
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

// ---------------------------------------------------------------------------
// 28. Intra-assignment delay on blocking assign (a = #5 b)
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_BlockingIntraAssignDelay) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
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
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

}  // namespace
