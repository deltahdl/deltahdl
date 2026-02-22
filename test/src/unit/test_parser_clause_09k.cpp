#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult9k {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult9k Parse(const std::string &src) {
  ParseResult9k result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FirstAlwaysItem(ParseResult9k &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      return item;
    }
  }
  return nullptr;
}

static Stmt *FirstInitialStmt(ParseResult9k &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
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
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff reset == 0) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff en) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with negedge
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardNegedge) {
  auto r = Parse("module m;\n"
                 "  always @(negedge clk iff !rst) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kNegedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with edge keyword
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardEdgeKeyword) {
  auto r = Parse("module m;\n"
                 "  always @(edge sig iff guard) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kEdge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with no edge qualifier (level-sensitive)
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardNoEdge) {
  auto r = Parse("module m;\n"
                 "  always @(sig iff en) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff (a && b)) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// Multiple events with iff on first only (or-separated)
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardMultipleOrFirst) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff en or negedge rst) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  always @(posedge clk or negedge rst iff !en) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r =
      Parse("module m;\n"
            "  always @(posedge clk iff en, negedge rst iff !mode) q <= d;\n"
            "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_NE(item->sensitivity[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with comparison operator
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardComparison) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff state == 2'b01) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard at always block level populates sensitivity vector
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardAlwaysSensitivity) {
  auto r =
      Parse("module m;\n"
            "  always @(posedge clk iff reset == 0 or posedge reset) begin\n"
            "    q <= d;\n"
            "  end\n"
            "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk iff en) q <= d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with comma-separated events at statement level
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardCommaStmtLevel) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk iff en, negedge rst) q <= d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
  EXPECT_EQ(stmt->events[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with or-separated events at statement level
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardOrStmtLevel) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk iff en or negedge rst) q <= d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
  EXPECT_EQ(stmt->events[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard in always_ff context
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardAlwaysFF) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clock iff reset == 0 or posedge reset) begin\n"
      "    r1 <= reset ? 0 : r2 + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with begin-end body
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardBeginEnd) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff en) begin\n"
                 "    a <= b;\n"
                 "    c <= d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// Verify iff_condition field is populated for posedge
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffConditionFieldPosedge) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff reset == 0) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  const auto &ev = item->sensitivity[0];
  // The iff_condition should be an equality comparison expression.
  ASSERT_NE(ev.iff_condition, nullptr);
  EXPECT_EQ(ev.iff_condition->kind, ExprKind::kBinary);
}

// ---------------------------------------------------------------------------
// Verify signal field is populated
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_SignalFieldPopulated) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff en) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  const auto &ev = item->sensitivity[0];
  ASSERT_NE(ev.signal, nullptr);
  EXPECT_EQ(ev.signal->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ev.signal->text, "clk");
}

// ---------------------------------------------------------------------------
// Verify edge field for negedge with iff
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_EdgeFieldNegedge) {
  auto r = Parse("module m;\n"
                 "  always @(negedge rst_n iff mode) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kNegedge);
  ASSERT_NE(item->sensitivity[0].signal, nullptr);
  EXPECT_EQ(item->sensitivity[0].signal->text, "rst_n");
}

// ---------------------------------------------------------------------------
// Multiple event expressions with mixed iff presence
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_MixedIffPresence) {
  auto r =
      Parse("module m;\n"
            "  always @(posedge clk iff en, negedge rst, edge sig iff guard)\n"
            "    q <= d;\n"
            "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 3u);
  // First: posedge clk iff en
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  // Second: negedge rst (no iff)
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
  EXPECT_EQ(item->sensitivity[1].iff_condition, nullptr);
  // Third: edge sig iff guard
  EXPECT_EQ(item->sensitivity[2].edge, Edge::kEdge);
  EXPECT_NE(item->sensitivity[2].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with logical-or condition expression
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardLogicalOr) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff (a || b)) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with not-equal comparison
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardNotEqual) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff state != 0) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  ASSERT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[0].iff_condition->kind, ExprKind::kBinary);
}

// ---------------------------------------------------------------------------
// iff guard at always_ff level with single posedge (no reset)
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardAlwaysFFSingleEdge) {
  auto r = Parse("module m;\n"
                 "  always_ff @(posedge clk iff en)\n"
                 "    q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard on no-edge event at statement level with comparison
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardNoEdgeStmtComparison) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(data iff enable == 1) y = data;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with unary negation in guard expression
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardUnaryNegation) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff !bypass) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  ASSERT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[0].iff_condition->kind, ExprKind::kUnary);
}

// ---------------------------------------------------------------------------
// iff guard with bitwise-and in guard expression
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardBitwiseAnd) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff (mask & enable)) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// ParseOk: three events all with iff guards (or-separated)
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardThreeEventsOr) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  always @(posedge a iff g1 or negedge b iff g2 or edge c iff g3)\n"
      "    q <= d;\n"
      "endmodule\n"));
}

// ---------------------------------------------------------------------------
// ParseOk: iff guard in always block with nonblocking assignment
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardNonblockingAssign) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  always @(posedge clk iff valid)\n"
                      "    data_out <= data_in;\n"
                      "endmodule\n"));
}

// ---------------------------------------------------------------------------
// Verify iff condition absent when not specified
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_NoIffConditionWhenAbsent) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// Verify body is preserved under iff guard at statement level
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_4_2_4_IffGuardStmtLevelBody) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(negedge clk iff active) begin\n"
                 "      a = 1;\n"
                 "      b = 2;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
  EXPECT_GE(stmt->body->stmts.size(), 2u);
}
