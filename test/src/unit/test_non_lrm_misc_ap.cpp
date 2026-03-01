// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FirstModuleItemOfKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static ModuleItem* FindClockingBlock(ParseResult& r, size_t idx = 0) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (count == idx) return item;
    ++count;
  }
  return nullptr;
}

namespace {

// assert #0 ( expression ) pass else fail ;
TEST(ParserA610, DeferredAssertHash0ActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 (1) $display(\"p\"); else $display(\"f\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// A.6.10 — deferred_immediate_assume_statement
// =============================================================================
// assume #0 ( expression ) ;
TEST(ParserA610, DeferredAssumeHash0) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// assume final ( expression ) ;
TEST(ParserA610, DeferredAssumeFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial assume final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// =============================================================================
// A.6.10 — deferred_immediate_cover_statement
// =============================================================================
// cover #0 ( expression ) ;
TEST(ParserA610, DeferredCoverHash0) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// cover final ( expression ) ;
TEST(ParserA610, DeferredCoverFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial cover final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// =============================================================================
// A.6.10 — action_block
// =============================================================================
// action_block: begin/end block as pass action
TEST(ParserA610, ActionBlockBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1) begin $display(\"a\"); $display(\"b\"); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt->kind, StmtKind::kBlock);
}

// action_block: [ statement ] else statement_or_null
TEST(ParserA610, ActionBlockPassFailBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1) begin end else begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// A.6.10 — concurrent_assertion_statement (module-level)
// =============================================================================
// assert_property_statement
TEST(ParserA610, AssertPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstModuleItemOfKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
}

// assume_property_statement
TEST(ParserA610, AssumePropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  assume property (req |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstModuleItemOfKind(r, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
}

// cover_property_statement
TEST(ParserA610, CoverPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a && b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstModuleItemOfKind(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
}

// cover_sequence_statement
TEST(ParserA610, CoverSequenceModule) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (a ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstModuleItemOfKind(r, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
}

// restrict_property_statement
TEST(ParserA610, RestrictPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstModuleItemOfKind(r, ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
}

// =============================================================================
// A.6.10 — deferred_immediate_assertion_item (module-level)
// =============================================================================
// assert #0 at module level
TEST(ParserA610, DeferredAssertHash0Module) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  assert #0 (x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// assert final at module level
TEST(ParserA610, DeferredAssertFinalModule) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  assert final (x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.10 — concurrent assertion with action_block
// =============================================================================
// assert property with pass and else actions
TEST(ParserA610, AssertPropertyActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a) $display(\"pass\"); else $display(\"fail\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstModuleItemOfKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_pass_stmt, nullptr);
  ASSERT_NE(item->assert_fail_stmt, nullptr);
}

// cover property with pass action only (no else)
TEST(ParserA610, CoverPropertyPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a) $display(\"covered\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstModuleItemOfKind(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_pass_stmt, nullptr);
}

// =============================================================================
// A.6.11 clocking_declaration — plain clocking block
// =============================================================================
TEST(ParserA611, ClockingDeclPlain) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
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
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
  EXPECT_EQ(item->name, "cb");
}

// =============================================================================
// A.6.11 clocking_declaration — global clocking
// =============================================================================
TEST(ParserA611, ClockingDeclGlobal) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
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
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
}

// =============================================================================
// A.6.11 clocking_declaration — end label
// =============================================================================
TEST(ParserA611, ClockingDeclEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking : cb\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");
}

// =============================================================================
// A.6.11 clocking_declaration — clocking_event as @identifier
// =============================================================================
TEST(ParserA611, ClockingEventBareIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @clk;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

// =============================================================================
// A.6.11 clocking_declaration — clocking_event as @(event_expression)
// =============================================================================
TEST(ParserA611, ClockingEventParenExpr) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kPosedge);
}

// =============================================================================
// A.6.11 clocking_item — default default_skew (input)
// =============================================================================
TEST(ParserA611, ClockingItemDefaultSkewInput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// =============================================================================
// A.6.11 clocking_item — default default_skew (output)
// =============================================================================
TEST(ParserA611, ClockingItemDefaultSkewOutput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default output #2;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "ack");
}

// =============================================================================
// A.6.11 clocking_item — default default_skew (input + output)
// =============================================================================
TEST(ParserA611, ClockingItemDefaultSkewInputOutput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1 output #2;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
}

// =============================================================================
// A.6.11 clocking_direction — input
// =============================================================================
TEST(ParserA611, ClockingDirectionInput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

}  // namespace
