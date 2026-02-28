// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult16b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16b Parse(const std::string& src) {
  ParseResult16b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =============================================================================
// Combination: property used with assert
// =============================================================================
TEST(ParserSection16, PropertyDeclAndAssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found_prop = false;
  bool found_assert = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) found_prop = true;
    if (item->kind == ModuleItemKind::kAssertProperty) found_assert = true;
  }
  EXPECT_TRUE(found_prop);
  EXPECT_TRUE(found_assert);
}

TEST(ParserSection16, OverviewAssertWithComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a inside {1, 2, 3});\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.4 Deferred assertions — additional forms
// =============================================================================
TEST(ParserSection16, DeferredAssumeHash0WithAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume #0 (valid) $display(\"assumed\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.4.1 Deferred assertion reporting
// =============================================================================
TEST(ParserSection16, DeferredAssertHash0PassAndFail) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert #0 (data_ok)\n"
      "      $display(\"pass\"); else $error(\"fail\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.5 Concurrent assertions overview — clocked property
// =============================================================================
TEST(ParserSection16, ConcurrentAssertWithClock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(ParserSection16, ConcurrentAssertNegedgeClock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(negedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.5.1 Concurrent assert/assume/cover
// =============================================================================
TEST(ParserSection16, ConcurrentAssumePropertyWithAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> gnt)\n"
      "    else $error(\"assumption failed\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

TEST(ParserSection16, ConcurrentCoverPropertyWithStmt) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
}

// =============================================================================
// §16.7 Sequences — concatenation and delay
// =============================================================================
TEST(ParserSection16, SequenceConcatDelay1) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##1 gnt ##1 !req);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceConcatDelay2) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##2 gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceDelayRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##[4:32] gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.9 Sequence operations — repetition
// =============================================================================
TEST(ParserSection16, SequenceConsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*3] |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceRepetitionRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*1:3] ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceGotoRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[->1]);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.9.4 Sequence throughout
// =============================================================================
TEST(ParserSection16, SequenceThroughoutBasic) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) !burst_mode throughout (##2 trdy[*7]));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceThroughoutInSeqDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence burst_rule;\n"
      "    @(posedge clk)\n"
      "    (!burst_mode) throughout (##2 (trdy && irdy)[*7]);\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* sq =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(sq, nullptr);
}

// =============================================================================
// §16.9.11 Sequence methods — triggered
// =============================================================================
TEST(ParserSection16, SequenceTriggeredMethod) {
  auto r = Parse(
      "module m;\n"
      "  sequence e1;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  sequence rule;\n"
      "    @(posedge clk) reset ##1 inst ##1 e1.triggered ##1 done;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceMatchedMethod) {
  auto r = Parse(
      "module m;\n"
      "  sequence e1;\n"
      "    @(posedge clk1) a ##1 b;\n"
      "  endsequence\n"
      "  sequence e2;\n"
      "    @(posedge clk2) reset ##1 e1.matched ##1 done;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.12 Property declarations — with formal arguments
// =============================================================================
TEST(ParserSection16, PropertyDeclWithFormals) {
  auto r = Parse(
      "module m;\n"
      "  property p_req_ack(req, ack);\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* pd =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->name, "p_req_ack");
}

TEST(ParserSection16, PropertyDeclWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty : p1\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.12.7 Property instances / implication
// =============================================================================
TEST(ParserSection16, PropertyOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyNonOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyInstanceWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  property p1(a, b);\n"
      "    a |-> ##1 b;\n"
      "  endproperty\n"
      "  assert property (@(posedge clk) p1(req, ack));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.13.6 Disable iff
// =============================================================================
TEST(ParserSection16, DisableIffInAssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, DisableIffInPropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    disable iff (rst == 2)\n"
      "    @(posedge clk) not (a ##1 b);\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, DisableIffWithComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst || !en)\n"
      "    req |-> ##[1:5] ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14 Concurrent assertions — procedural context
// =============================================================================
// =============================================================================
// §16.14.2 Sequence property — strong/weak
// =============================================================================
TEST(ParserSection16, StrongSequenceProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) strong(a ##1 b ##1 c));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, WeakSequenceProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) weak(a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14.6 Property case
// =============================================================================
TEST(ParserSection16, PropertyCaseBasic) {
  auto r = Parse(
      "module m;\n"
      "  property p_delay(logic [1:0] delay);\n"
      "    case (delay)\n"
      "      2'd0 : a && b;\n"
      "      2'd1 : a ##2 b;\n"
      "      2'd2 : a ##4 b;\n"
      "      default: 0;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyCaseInAssert) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk)\n"
      "    case (mode)\n"
      "      2'b00 : a |-> b;\n"
      "      2'b01 : a |-> ##1 b;\n"
      "      2'b10 : a |-> ##2 b;\n"
      "    endcase\n"
      "  endproperty\n"
      "  assert property (p1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14.6.2 Property if-else
// =============================================================================
TEST(ParserSection16, PropertyIfElse) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk)\n"
      "    if (mode) a |-> b\n"
      "    else a |-> c);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyIfWithoutElse) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk)\n"
      "    if (en) a |-> ##[1:3] b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyIfElseInDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk)\n"
      "    if (sel)\n"
      "      req |-> ##1 ack\n"
      "    else\n"
      "      req |-> ##2 ack;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14.7 Property negation
// =============================================================================
TEST(ParserSection16, PropertyNegation) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not (a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyNegationStrong) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not strong(a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14.8 Property disjunction and conjunction
// =============================================================================
TEST(ParserSection16, PropertyDisjunction) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) or (c |-> d));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyConjunction) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) and (c |-> d));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyDisjunctionAndConjunctionCombined) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk)\n"
      "    ((a |-> b) and (c |-> d)) or (e |-> f));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.9 -- System functions for assertions ($sampled, $rose, $fell, $stable)
// =============================================================================
TEST(ParserSection16, SampledFunctionInAssert) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    else $error(\"a=%b b=%b\", $sampled(a), $sampled(b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, RoseFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $rose(req) |-> ##[1:3] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, FellFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $fell(req) |-> ##1 !ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, StableFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $stable(data) |-> valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, PastFunctionWithTicks) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $past(req, 2) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, ChangedFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $changed(data) |-> valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.12 -- Declaring sequences (additional tests)
// =============================================================================
TEST(ParserSection16, SequenceWithRangeDelay) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_handshake;\n"
      "    req ##[1:5] ack;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      found = true;
      EXPECT_EQ(item->name, "s_handshake");
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection16, SequenceWithFormalArgsDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_req_ack(req, ack);\n"
      "    req ##1 ack;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, SequenceUsedInPropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "  property p1;\n"
      "    @(posedge clk) s1 |=> c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.14 -- Declaring properties (additional tests)
// =============================================================================
TEST(ParserSection16, PropertyWithDisableIffDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p_req_ack;\n"
      "    @(posedge clk) disable iff (rst)\n"
      "    req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, PropertyWithFormalArgsDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p_valid(signal, valid);\n"
      "    @(posedge clk) signal |-> valid;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.14.6.2 -- Multiclock support
// =============================================================================
TEST(ParserSection16, MultichannelAssertPropertyInline) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk1) a ##1 @(posedge clk2) b\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, MulticlockPropertyDeclImplication) {
  auto r = Parse(
      "module m;\n"
      "  property p_multi;\n"
      "    @(posedge clk1) req |=> @(posedge clk2) ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, MulticlockSequenceDeclTwo) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_multi;\n"
      "    @(posedge clk1) a ##1 @(posedge clk2) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.14.7 -- Inferred clocking and disable functions
// =============================================================================
TEST(ParserSection16, InferredClockInProperty) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p_inferred(clk_ev = $inferred_clock);\n"
      "    @clk_ev a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, InferredDisableInProperty) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "  property p_dis(rst_cond = $inferred_disable);\n"
      "    disable iff (rst_cond) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, InferredClockAndDisableTogether) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(negedge clk); endclocking\n"
      "  default disable iff rst;\n"
      "  property p_both(c = $inferred_clock, d = $inferred_disable);\n"
      "    @c disable iff (d) req |-> ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.9.4 -- Sequence throughout (additional tests)
// =============================================================================
TEST(ParserSection16, SequenceThroughoutWithImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) req |-> en throughout (##2 ack[*3]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
