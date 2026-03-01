// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static Stmt* NthInitialStmt(ParseResult9j& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

struct ParseResult9k {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9k Parse(const std::string& src) {
  ParseResult9k result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysItem(ParseResult9k& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      return item;
    }
  }
  return nullptr;
}

static Stmt* FirstInitialStmt(ParseResult9k& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

namespace {

// Verify is_star_event is true and events empty for @(*) at statement level
TEST(ParserSection9, Sec9_4_2_3_IsStarEventTrueAtStarParen) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_EQ(stmt->events.size(), 0u);
}

// @* body is present for statement-level event control
TEST(ParserSection9, Sec9_4_2_3_AtStarStmtBodyPresent) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlockingAssign);
}

// @* statement level with begin-end block
TEST(ParserSection9, Sec9_4_2_3_AtStarStmtLevelBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    @* begin\n"
      "      a = b;\n"
      "      c = a;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->body->stmts.size(), 2u);
}

// Multiple @* event controls in sequence inside initial block
TEST(ParserSection9, Sec9_4_2_3_MultipleAtStarInInitial) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "    @(*) c = d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kEventControl);
  EXPECT_TRUE(s0->is_star_event);
  EXPECT_EQ(s1->kind, StmtKind::kEventControl);
  EXPECT_TRUE(s1->is_star_event);
}

// ParseOk: @* parses without errors in a typical combinational module
TEST(ParserSection9, Sec9_4_2_3_ParseOkAtStarCombiModule) {
  EXPECT_TRUE(
      ParseOk("module mux4(\n"
              "  input [1:0] sel,\n"
              "  input [7:0] a, b, c, d,\n"
              "  output reg [7:0] out\n"
              ");\n"
              "  always @* begin\n"
              "    case (sel)\n"
              "      2'd0: out = a;\n"
              "      2'd1: out = b;\n"
              "      2'd2: out = c;\n"
              "      default: out = d;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

// ParseOk: @(*) parses without errors in a typical combinational module
TEST(ParserSection9, Sec9_4_2_3_ParseOkAtStarParenCombiModule) {
  EXPECT_TRUE(
      ParseOk("module adder(\n"
              "  input [7:0] a, b,\n"
              "  output reg [8:0] sum\n"
              ");\n"
              "  always @(*) begin\n"
              "    sum = a + b;\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 9.4.2.4 -- Conditional event controls (iff guard)
//
// event_expression ::= [ edge_identifier ] expression [ iff expression ]
//
// The iff guard filters the event so the associated statement only triggers
// when the guard condition is true at the moment of the edge.
// =============================================================================
// ---------------------------------------------------------------------------
// Basic iff guard with posedge
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardPosedgeBasic) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff reset == 0) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].signal, nullptr);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with posedge and simple enable signal
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardPosedgeEnable) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with negedge
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardNegedge) {
  auto r = Parse(
      "module m;\n"
      "  always @(negedge clk iff !rst) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kNegedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with edge keyword
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardEdgeKeyword) {
  auto r = Parse(
      "module m;\n"
      "  always @(edge sig iff guard) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kEdge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with no edge qualifier (level-sensitive)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardNoEdge) {
  auto r = Parse(
      "module m;\n"
      "  always @(sig iff en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kNone);
  EXPECT_NE(item->sensitivity[0].signal, nullptr);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with complex parenthesized condition
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardComplexCondition) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff (a && b)) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// Multiple events with iff on first only (or-separated)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardMultipleOrFirst) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff en or negedge rst) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
  EXPECT_EQ(item->sensitivity[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// Multiple events with iff on second only (or-separated)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardMultipleOrSecond) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk or negedge rst iff !en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
  EXPECT_NE(item->sensitivity[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// Multiple events with iff on both (comma-separated)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardBothComma) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff en, negedge rst iff !mode) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_NE(item->sensitivity[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with comparison operator
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardComparison) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff state == 2'b01) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard at always block level populates sensitivity vector
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardAlwaysSensitivity) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff reset == 0 or posedge reset) begin\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  // The sensitivity list should have two entries.
  ASSERT_EQ(item->sensitivity.size(), 2u);
  // First event has iff guard.
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  // Second event has no iff guard.
  EXPECT_EQ(item->sensitivity[1].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kPosedge);
}

// ---------------------------------------------------------------------------
// iff guard at statement level inside initial (populates Stmt::events)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardStmtLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk iff en) q <= d;\n"
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

}  // namespace
