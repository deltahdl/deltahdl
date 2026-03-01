// §9.4.2: Event control

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// edge_identifier ::= posedge | negedge | edge
// ---------------------------------------------------------------------------
// §9.4.2: all three edge identifiers parsed correctly
TEST(ParserA605, EdgeIdentifiers) {
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

static ModuleItem* FirstAlwaysItem(ParseResult9c& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

// =============================================================================
// §9.4.2 -- edge keyword in event control
// =============================================================================
TEST(ParserSection9, EventControlEdge) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] a;\n"
      "  wire clk;\n"
      "  always @(edge clk) a = ~a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kEdge);
}

struct ParseResult9d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9d Parse(const std::string& src) {
  ParseResult9d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialBody(ParseResult9d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) return item->body;
  }
  return nullptr;
}

static Stmt* FirstInitialStmt(ParseResult9d& r) {
  auto* body = FirstInitialBody(r);
  if (body && body->kind == StmtKind::kBlock) {
    return body->stmts.empty() ? nullptr : body->stmts[0];
  }
  return body;
}

// =============================================================================
// LRM section 9.4.2 -- Event control
// Named event trigger and bare @identifier event control.
// =============================================================================
TEST(ParserSection9c, EventControlAtIdentifier) {
  // @clk shorthand for @(clk)
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @clk a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
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

TEST(ParserSection9, EventControlBareSignal) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(data) a = data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
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
// 11. @(posedge clk) event control
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_PosedgeEventControl) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a;\n"
      "  initial begin\n"
      "    @(posedge clk) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_NE(stmt->body, nullptr);
}

// ---------------------------------------------------------------------------
// 12. @(negedge clk) event control
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_NegedgeEventControl) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a;\n"
      "  initial begin\n"
      "    @(negedge clk) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  EXPECT_NE(stmt->body, nullptr);
}

// =============================================================================
// LRM section 9.4.2 -- Event control (additional edge cases)
// Null statement after event control, back-to-back event controls.
// =============================================================================
TEST(ParserSection9c, EventControlNullStatement) {
  // @(posedge clk); -- event control with null statement (just a semicolon)
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk);\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

TEST(ParserSection9c, BackToBackEventControls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk);\n"
      "    @(posedge clk);\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kEventControl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kEventControl);
}

struct ParseResult90301 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult90301 Parse(const std::string& src) {
  ParseResult90301 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

TEST(Parser, EventWaitWithParens) {
  auto r = Parse(
      "module t;\n"
      "  event ev;\n"
      "  initial @(ev) ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[1];
  auto* stmt = item->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}

// §9.4.2: procedural_timing_control_statement (event control)
TEST(ParserA604, StmtItemProceduralTimingControlEvent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

// §9.4.2: event control followed by statement
TEST(ParserA605, ProceduralTimingControlEvent) {
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
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_FALSE(stmt->events.empty());
  EXPECT_NE(stmt->body, nullptr);
}

// §9.4.2: event control followed by null statement
TEST(ParserA605, ProceduralTimingControlEventNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

// §9.4.2: @identifier simple event control
TEST(ParserA605, EventControlBareIdentifier) {
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

// §9.4.2: @(expression) parenthesized event control
TEST(ParserA605, EventControlParenthesized) {
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

// ---------------------------------------------------------------------------
// clocking_event ::=
//   @ ps_identifier | @ hierarchical_identifier | @ ( event_expression )
// ---------------------------------------------------------------------------
// §9.4.2: @(posedge clk) — clocking event with edge
TEST(ParserA605, ClockingEventPosedge) {
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

// §9.4.2: @(negedge clk) — clocking event with negedge
TEST(ParserA605, ClockingEventNegedge) {
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

// ---------------------------------------------------------------------------
// event_expression ::=
//   [ edge_identifier ] expression [ iff expression ]
//   | sequence_instance [ iff expression ]
//   | event_expression or event_expression
//   | event_expression , event_expression
//   | ( event_expression )
// ---------------------------------------------------------------------------
// §9.4.2: edge_identifier = edge (generic)
TEST(ParserA605, EventExprEdge) {
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

// §9.4.2: expression without edge (any change)
TEST(ParserA605, EventExprAnyChange) {
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

}  // namespace
