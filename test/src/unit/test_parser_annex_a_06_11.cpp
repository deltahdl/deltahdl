#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem *FindClockingBlock(ParseResult &r, size_t idx = 0) {
  size_t count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kClockingBlock)
      continue;
    if (count == idx)
      return item;
    ++count;
  }
  return nullptr;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
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

} // namespace

// =============================================================================
// A.6.11 clocking_declaration — plain clocking block
// =============================================================================

TEST(ParserA611, ClockingDeclPlain) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kClockingBlock);
  EXPECT_EQ(item->name, "cb");
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
}

// =============================================================================
// A.6.11 clocking_declaration — default clocking
// =============================================================================

TEST(ParserA611, ClockingDeclDefault) {
  auto r = Parse("module m;\n"
                 "  default clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
  EXPECT_EQ(item->name, "cb");
}

// =============================================================================
// A.6.11 clocking_declaration — global clocking
// =============================================================================

TEST(ParserA611, ClockingDeclGlobal) {
  auto r = Parse("module m;\n"
                 "  global clocking gclk @(posedge sys_clk);\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_EQ(item->name, "gclk");
  EXPECT_TRUE(item->clocking_signals.empty());
}

// =============================================================================
// A.6.11 clocking_declaration — unnamed default clocking
// =============================================================================

TEST(ParserA611, ClockingDeclUnnamed) {
  auto r = Parse("module m;\n"
                 "  default clocking @(posedge clk);\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
}

// =============================================================================
// A.6.11 clocking_declaration — end label
// =============================================================================

TEST(ParserA611, ClockingDeclEndLabel) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "  endclocking : cb\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");
}

// =============================================================================
// A.6.11 clocking_declaration — clocking_event as @identifier
// =============================================================================

TEST(ParserA611, ClockingEventBareIdentifier) {
  auto r = Parse("module m;\n"
                 "  clocking cb @clk;\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

// =============================================================================
// A.6.11 clocking_declaration — clocking_event as @(event_expression)
// =============================================================================

TEST(ParserA611, ClockingEventParenExpr) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kPosedge);
}

// =============================================================================
// A.6.11 clocking_item — default default_skew (input)
// =============================================================================

TEST(ParserA611, ClockingItemDefaultSkewInput) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    default input #1;\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// =============================================================================
// A.6.11 clocking_item — default default_skew (output)
// =============================================================================

TEST(ParserA611, ClockingItemDefaultSkewOutput) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    default output #2;\n"
                 "    output ack;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "ack");
}

// =============================================================================
// A.6.11 clocking_item — default default_skew (input + output)
// =============================================================================

TEST(ParserA611, ClockingItemDefaultSkewInputOutput) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    default input #1 output #2;\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
}

// =============================================================================
// A.6.11 clocking_direction — input
// =============================================================================

TEST(ParserA611, ClockingDirectionInput) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// =============================================================================
// A.6.11 clocking_direction — output
// =============================================================================

TEST(ParserA611, ClockingDirectionOutput) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output ack;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[0].name, "ack");
}

// =============================================================================
// A.6.11 clocking_direction — input [skew] output [skew]
// =============================================================================

TEST(ParserA611, ClockingDirectionInputOutput) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input #2 output #4 cmd;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInout);
  EXPECT_EQ(sig.name, "cmd");
  EXPECT_NE(sig.skew_delay, nullptr);
  EXPECT_NE(sig.out_skew_delay, nullptr);
}

// =============================================================================
// A.6.11 clocking_direction — inout
// =============================================================================

TEST(ParserA611, ClockingDirectionInout) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    inout bidir;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[0].name, "bidir");
}

// =============================================================================
// A.6.11 list_of_clocking_decl_assign — single signal
// =============================================================================

TEST(ParserA611, ListOfClockingDeclAssignSingle) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// =============================================================================
// A.6.11 list_of_clocking_decl_assign — multiple comma-separated signals
// =============================================================================

TEST(ParserA611, ListOfClockingDeclAssignMultiple) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input a, b, c;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  EXPECT_EQ(item->clocking_signals[0].name, "a");
  EXPECT_EQ(item->clocking_signals[1].name, "b");
  EXPECT_EQ(item->clocking_signals[2].name, "c");
}

// =============================================================================
// A.6.11 clocking_decl_assign — signal_identifier only
// =============================================================================

TEST(ParserA611, ClockingDeclAssignBare) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
  EXPECT_EQ(item->clocking_signals[0].hier_expr, nullptr);
}

// =============================================================================
// A.6.11 clocking_decl_assign — signal_identifier = expression
// =============================================================================

TEST(ParserA611, ClockingDeclAssignWithHierExpr) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input enable = top.dut.enable;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "enable");
  EXPECT_NE(item->clocking_signals[0].hier_expr, nullptr);
}

// =============================================================================
// A.6.11 clocking_skew — edge_identifier only (posedge)
// =============================================================================

TEST(ParserA611, ClockingSkewEdgeOnly) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output posedge ack;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  EXPECT_EQ(sig.skew_edge, Edge::kPosedge);
  EXPECT_EQ(sig.skew_delay, nullptr);
}

// =============================================================================
// A.6.11 clocking_skew — delay_control only
// =============================================================================

TEST(ParserA611, ClockingSkewDelayOnly) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input #3 data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  EXPECT_EQ(sig.skew_edge, Edge::kNone);
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->kind, ExprKind::kIntegerLiteral);
}

// =============================================================================
// A.6.11 clocking_skew — edge_identifier + delay_control
// =============================================================================

TEST(ParserA611, ClockingSkewEdgeAndDelay) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output negedge #1 ack;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  EXPECT_EQ(sig.skew_edge, Edge::kNegedge);
  ASSERT_NE(sig.skew_delay, nullptr);
}

// =============================================================================
// A.6.11 clocking_skew — #1step special form
// =============================================================================

TEST(ParserA611, ClockingSkew1step) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input #1step data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->text, "1step");
}

// =============================================================================
// A.6.11 clocking_drive — clockvar_expression <= expression
// =============================================================================

TEST(ParserA611, ClockingDriveSimple) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output data;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    cb.data <= 8'hFF;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

// =============================================================================
// A.6.11 clocking_drive — clockvar_expression <= cycle_delay expression
// =============================================================================

TEST(ParserA611, ClockingDriveWithCycleDelay) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output data;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    cb.data <= ##2 8'hFF;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->cycle_delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

// =============================================================================
// A.6.11 cycle_delay — ## integral_number
// =============================================================================

TEST(ParserA611, CycleDelayNumber) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output data;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    cb.data <= ##3 8'h42;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.11 cycle_delay — ## identifier
// =============================================================================

TEST(ParserA611, CycleDelayIdentifier) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output data;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    cb.data <= ##n 8'h42;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.11 cycle_delay — ## ( expression )
// =============================================================================

TEST(ParserA611, CycleDelayParenExpr) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output data;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    cb.data <= ##(n+1) 8'h42;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.11 clockvar / clockvar_expression — hierarchical access
// =============================================================================

TEST(ParserA611, ClockvarExpression) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output data;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    cb.data <= 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
}

// =============================================================================
// A.6.11 clocking_declaration — default clocking reference form
// =============================================================================

TEST(ParserA611, DefaultClockingReference) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "  endclocking\n"
                 "  default clocking cb;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.11 clocking_declaration — multiple direction groups
// =============================================================================

TEST(ParserA611, MultipleDirectionGroups) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input a;\n"
                 "    output b;\n"
                 "    inout c;\n"
                 "    input #2 output #4 d;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 4u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[1].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[2].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[3].direction, Direction::kInout);
}

// =============================================================================
// A.6.11 clocking_direction — input with skew, no output
// =============================================================================

TEST(ParserA611, InputWithSkewNoOutput) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input posedge #2 data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  EXPECT_EQ(sig.skew_edge, Edge::kPosedge);
  ASSERT_NE(sig.skew_delay, nullptr);
}

// =============================================================================
// A.6.11 global clocking — unnamed with negedge
// =============================================================================

TEST(ParserA611, GlobalClockingUnnamed) {
  auto r = Parse("module m;\n"
                 "  global clocking @(negedge clk); endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->name.empty());
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

// =============================================================================
// A.6.11 global clocking — compound event expression
// =============================================================================

TEST(ParserA611, GlobalClockingCompoundEvent) {
  auto r = Parse("module m;\n"
                 "  global clocking sys @(clk1 or clk2); endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_GE(item->clocking_event.size(), 2u);
}

// =============================================================================
// A.6.11 clocking_decl_assign — multiple with mixed hier_expr
// =============================================================================

TEST(ParserA611, ClockingDeclAssignMultipleMixed) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input a, b = top.sig_b, c;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  EXPECT_EQ(item->clocking_signals[0].hier_expr, nullptr);
  EXPECT_NE(item->clocking_signals[1].hier_expr, nullptr);
  EXPECT_EQ(item->clocking_signals[2].hier_expr, nullptr);
}

// =============================================================================
// A.6.11 clocking_item — assertion_item_declaration (property_declaration)
// =============================================================================

TEST(ParserA611, ClockingItemPropertyDecl) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "    property p;\n"
                 "      data;\n"
                 "    endproperty\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

// =============================================================================
// A.6.11 clocking_item — assertion_item_declaration (sequence_declaration)
// =============================================================================

TEST(ParserA611, ClockingItemSequenceDecl) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "    sequence s;\n"
                 "      data;\n"
                 "    endsequence\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

// =============================================================================
// A.6.11 clocking_item — assertion_item_declaration (let_declaration)
// =============================================================================

TEST(ParserA611, ClockingItemLetDecl) {
  auto r = Parse("module m;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    input data;\n"
                 "    let valid = data;\n"
                 "  endclocking\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}
