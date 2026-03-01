// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.11 clocking_direction — input with skew, no output
// =============================================================================
TEST(ParserA611, InputWithSkewNoOutput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input posedge #2 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  EXPECT_EQ(sig.skew_edge, Edge::kPosedge);
  ASSERT_NE(sig.skew_delay, nullptr);
}

// =============================================================================
// A.6.11 global clocking — unnamed with negedge
// =============================================================================
TEST(ParserA611, GlobalClockingUnnamed) {
  auto r = Parse(
      "module m;\n"
      "  global clocking @(negedge clk); endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
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
  auto r = Parse(
      "module m;\n"
      "  global clocking sys @(clk1 or clk2); endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_GE(item->clocking_event.size(), 2u);
}

// =============================================================================
// A.6.11 clocking_decl_assign — multiple with mixed hier_expr
// =============================================================================
TEST(ParserA611, ClockingDeclAssignMultipleMixed) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, b = top.sig_b, c;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
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
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    property p;\n"
      "      data;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

// =============================================================================
// A.6.11 clocking_item — assertion_item_declaration (sequence_declaration)
// =============================================================================
TEST(ParserA611, ClockingItemSequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    sequence s;\n"
      "      data;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

// =============================================================================
// A.6.11 clocking_item — assertion_item_declaration (let_declaration)
// =============================================================================
TEST(ParserA611, ClockingItemLetDecl) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    let valid = data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

// =============================================================================
// A.6.12 Randsequence — randsequence_statement
// =============================================================================
// randsequence ( production_identifier ) production+ endsequence
TEST(ParserA612, RandsequenceStmtWithName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { $display(\"first\"); };\n"
      "      second : { $display(\"second\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandsequence);
}

// randsequence ( ) production+ endsequence — no production name
TEST(ParserA612, RandsequenceStmtNoName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence()\n"
      "      main : first;\n"
      "      first : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandsequence);
}

// =============================================================================
// A.6.12 Randsequence — rs_production
// =============================================================================
// Production with return type: int P : ...;
TEST(ParserA612, RsProductionWithReturnType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      int main : gen;\n"
      "      gen : { return 42; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Production with port list: P(int x) : ...;
TEST(ParserA612, RsProductionWithPorts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen(5);\n"
      "      void gen(int x) : { $display(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_rule (multiple alternatives with |)
// =============================================================================
// Multiple rules separated by |
TEST(ParserA612, RsRuleMultipleAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a | b | c;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_production_list
// =============================================================================
// Sequence of production items
TEST(ParserA612, RsProductionListSequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a b c;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rand join production list
TEST(ParserA612, RsProductionListRandJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join a b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rand join ( expression ) with bias
TEST(ParserA612, RsProductionListRandJoinWithExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join (1) a b c;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_weight_specification
// =============================================================================
// Weight as integral number
TEST(ParserA612, RsWeightIntegralNumber) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 3 | b := 7;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Weight as identifier
TEST(ParserA612, RsWeightIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  int w = 5;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := w | b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Weight as parenthesized expression
TEST(ParserA612, RsWeightParenExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := (2 + 3) | b := (1);\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_code_block
// =============================================================================
// Code block with data declaration and statement
TEST(ParserA612, RsCodeBlockWithDataDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { int x; x = 5; $display(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Weight with code block
TEST(ParserA612, RsWeightWithCodeBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 5 { $display(\"chose a\"); }\n"
      "           | b := 3 { $display(\"chose b\"); };\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_prod (all alternatives)
// =============================================================================
// rs_prod as rs_production_item
TEST(ParserA612, RsProdAsProductionItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rs_prod as rs_code_block
TEST(ParserA612, RsProdAsCodeBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { $display(\"inline\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rs_prod as rs_if_else
TEST(ParserA612, RsProdAsIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) a else b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rs_prod as rs_repeat
TEST(ParserA612, RsProdAsRepeat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(3) child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rs_prod as rs_case
TEST(ParserA612, RsProdAsCase) {
  auto r = Parse(
      "module m;\n"
      "  int sel = 1;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (sel) 0: a; 1: b; default: c; endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_production_item
// =============================================================================
// Production item with arguments
TEST(ParserA612, RsProductionItemWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen(1, 2);\n"
      "      void gen(int a, int b) : { $display(a + b); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Production item bare (no arguments)
TEST(ParserA612, RsProductionItemBare) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_if_else
// =============================================================================
// if without else
TEST(ParserA612, RsIfOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// if with else
TEST(ParserA612, RsIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (0) a else b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_repeat
// =============================================================================
// repeat with integral expression
TEST(ParserA612, RsRepeat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(5) child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_case
// =============================================================================
// Case with multiple items
TEST(ParserA612, RsCaseMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (1)\n"
      "               0: a;\n"
      "               1: b;\n"
      "               2: c;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_case_item
// =============================================================================
// Case item with comma-separated expressions
TEST(ParserA612, RsCaseItemCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (1)\n"
      "               0, 1: a;\n"
      "               2, 3: b;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
