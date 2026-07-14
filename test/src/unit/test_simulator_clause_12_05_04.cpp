

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CaseInsideStatementSim, CaseInsideValueMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case(sel) inside\n"
      "      8'd1, 8'd3: x = 8'd10;\n"
      "      8'd5: x = 8'd20;\n"
      "      default: x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseInsideStatementSim, CaseInsideNoMatchFallsToDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    case(sel) inside\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd5: x = 8'd20;\n"
      "      default: x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(CaseInsideStatementSim, CaseInsideCommaValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd3;\n"
      "    case(sel) inside\n"
      "      8'd1, 8'd3, 8'd5: x = 8'd10;\n"
      "      8'd7: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case(sel) inside\n"
      "      [8'd3:8'd7]: x = 8'd10;\n"
      "      default: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd10;\n"
      "    case(sel) inside\n"
      "      [8'd3:8'd7]: x = 8'd10;\n"
      "      default: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseInsideStatementSim, CaseInsideWildcardInPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 3'b100;\n"
      "    case(sel) inside\n"
      "      3'b1??: x = 3'd1;\n"
      "      default: x = 3'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideXInSelectorNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 3'bx00;\n"
      "    x = 3'd0;\n"
      "    case(sel) inside\n"
      "      3'b100: x = 3'd1;\n"
      "      3'b000: x = 3'd2;\n"
      "      default: x = 3'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(CaseInsideStatementSim, CaseInsideFirstMatchWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case(sel) inside\n"
      "      [8'd0:8'd10]: x = 8'd1;\n"
      "      [8'd3:8'd7]:  x = 8'd2;\n"
      "      default: x = 8'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeBoundaryLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd3;\n"
      "    case(sel) inside\n"
      "      [8'd3:8'd7]: x = 8'd1;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeBoundaryHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd7;\n"
      "    case(sel) inside\n"
      "      [8'd3:8'd7]: x = 8'd1;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeBelowLowNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd2;\n"
      "    case(sel) inside\n"
      "      [8'd3:8'd7]: x = 8'd1;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(CaseInsideStatementSim, CaseInsideOpenEndedLowRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd0;\n"
      "    case(sel) inside\n"
      "      [$:8'd5]: x = 8'd1;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideOpenEndedHighRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd255;\n"
      "    case(sel) inside\n"
      "      [8'd200:$]: x = 8'd1;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideTolerancePlusMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd7;\n"
      "    case(sel) inside\n"
      "      [8'd5 +/- 8'd2]: x = 8'd1;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideTolerancePlusMinusOutOfRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd8;\n"
      "    case(sel) inside\n"
      "      [8'd5 +/- 8'd2]: x = 8'd1;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(CaseInsideStatementSim, CaseInsideTolerancePlusPercentMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd55;\n"
      "    case(sel) inside\n"
      "      [8'd50 +%- 8'd10]: x = 8'd1;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideTolerancePlusPercentMinusOutOfRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd56;\n"
      "    case(sel) inside\n"
      "      [8'd50 +%- 8'd10]: x = 8'd1;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §12.5.4: the set-membership comparison is evaluated in the order specified by
// a priority-case statement. A priority-qualified case-inside acts on the first
// matching item even when later items also match (mirrors the LRM example,
// which qualifies a case-inside with priority).
TEST(CaseInsideStatementSim, CaseInsidePriorityFirstMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    priority case(sel) inside\n"
      "      [8'd0:8'd10]: x = 8'd1;\n"
      "      [8'd3:8'd7]:  x = 8'd2;\n"
      "      default: x = 8'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.5.4: the set-membership comparison is evaluated in the order specified by
// a unique-case statement. A unique-qualified case-inside selects the single
// matching item through the unique evaluation path, with the inside operator
// performing the comparison.
TEST(CaseInsideStatementSim, CaseInsideUniqueSingleMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    unique case(sel) inside\n"
      "      8'd1, 8'd3: x = 8'd10;\n"
      "      8'd5:       x = 8'd20;\n"
      "      default:    x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.5.4: the comparison uses asymmetric wildcard matching (11.4.6), so an
// unknown (x or z) bit on the case_expression side that lands on a position the
// case_item wildcards out is not compared and the item still matches. This
// mirrors the LRM's case-inside example where pattern 'b0?0 matches selector
// values including 'b0x0 and 'b0z0.
TEST(CaseInsideStatementSim, CaseInsideWildcardMasksSelectorXBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 3'b0x0;\n"
      "    x = 3'd0;\n"
      "    case(sel) inside\n"
      "      3'b0?0: x = 3'd1;\n"
      "      default: x = 3'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.5.4: a single case_item's range_list may list several heterogeneous
// elements (a wildcard value and a bracketed range here); the case_expression
// is compared against each and the item matches when any comparison returns
// 1'b1. This is the exact shape of the LRM case-inside example item
// "3'b0?0, [4:7]", matched here through its range element.
TEST(CaseInsideStatementSim, CaseInsideMixedValueAndRangeItem) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 3'd6;\n"
      "    x = 3'd0;\n"
      "    case(sel) inside\n"
      "      3'b0?0, [4:7]: x = 3'd1;\n"
      "      default: x = 3'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.5.4 C1: a case_item value need not be a literal. Here the item is a
// parameter, so the right operand of the inside comparison is produced by
// parameter elaboration rather than a literal token — a distinct value-source
// path that must still be compared against the case_expression.
TEST(CaseInsideStatementSim, CaseInsideValueFromParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 8'd5;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    x = 8'd0;\n"
      "    case(sel) inside\n"
      "      P: x = 8'd1;\n"
      "      default: x = 8'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.5.4 C1: the bounds of a case_item range may themselves be elaborated
// constants (localparams here) rather than literals, exercising the range
// comparison with bounds resolved through parameter elaboration.
TEST(CaseInsideStatementSim, CaseInsideRangeBoundsFromLocalparam) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam LO = 8'd3, HI = 8'd7;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    x = 8'd0;\n"
      "    case(sel) inside\n"
      "      [LO:HI]: x = 8'd1;\n"
      "      default: x = 8'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.5.4 C1 consuming the §11.4.13 inside-operator machinery end to end: a
// case_item that names an unpacked array (built here from a real '{...}
// initializer) is a set whose elements are each compared against the
// case_expression, and the item matches when the value equals any element. The
// array is created through real declaration syntax and driven through the full
// pipeline, not hand-built.
TEST(CaseInsideStatementSim, CaseInsideArraySetMemberMatches) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr[3] = '{1, 5, 9};\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    x = 8'd0;\n"
      "    case(sel) inside\n"
      "      arr: x = 8'd1;\n"
      "      default: x = 8'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.5.4 C1/§11.4.13: no element of the array set equals the case_expression,
// so the item does not match and control falls to default. Confirms the array
// set-member path also produces the no-match result, not just a match.
TEST(CaseInsideStatementSim, CaseInsideArraySetMemberNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr[3] = '{1, 5, 9};\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd4;\n"
      "    x = 8'd0;\n"
      "    case(sel) inside\n"
      "      arr: x = 8'd1;\n"
      "      default: x = 8'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.5.4 C5 negative form: the default clause is executed only when it is
// given. With no matching item and no default present, none of the case_item
// statements run and the target retains its prior value.
TEST(CaseInsideStatementSim, CaseInsideNoMatchNoDefaultLeavesTargetUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    x = 8'd42;\n"
      "    case(sel) inside\n"
      "      8'd1: x = 8'd1;\n"
      "      8'd2: x = 8'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CaseInsideStatementSim, CaseInsideEmptyNoItems) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    x = 8'd99;\n"
      "    case(sel) inside\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

}  // namespace
