#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CaseInsideStatementSim, CaseInsideValueMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseInsideStatementSim, CaseInsideNoMatchFallsToDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(CaseInsideStatementSim, CaseInsideCommaValues) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeNoMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseInsideStatementSim, CaseInsideWildcardInPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideXInSelectorNoMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(CaseInsideStatementSim, CaseInsideFirstMatchWins) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeBoundaryLow) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeBoundaryHigh) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeBelowLowNoMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(CaseInsideStatementSim, CaseInsideOpenEndedLowRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideOpenEndedHighRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideTolerancePlusMinus) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideTolerancePlusMinusOutOfRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(CaseInsideStatementSim, CaseInsideTolerancePlusPercentMinus) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideTolerancePlusPercentMinusOutOfRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(CaseInsideStatementSim, CaseInsidePriorityFirstMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideUniqueSingleMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseInsideStatementSim, CaseInsideWildcardMasksSelectorXBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideMixedValueAndRangeItem) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideValueFromParameter) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideRangeBoundsFromLocalparam) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideArraySetMemberMatches) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseInsideStatementSim, CaseInsideArraySetMemberNoMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(CaseInsideStatementSim, CaseInsideNoMatchNoDefaultLeavesTargetUnchanged) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CaseInsideExampleSim, ThePriorityCaseInsideExampleMatchesWithWildcards) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  logic [2:0] status;\n"
          "  task task1; $display(\"task1 %b\", status); endtask\n"
          "  task task2; $display(\"task2 %b\", status); endtask\n"
          "  task check(input logic [2:0] v);\n"
          "    status = v;\n"
          "    priority case (status) inside\n"
          "      1, 3 :         task1;\n"
          "      3'b0?0, [4:7]: task2;\n"
          "    endcase\n"
          "  endtask\n"
          "  initial begin\n"
          "    check(3'b001); check(3'b011); check(3'b000); check(3'b010);\n"
          "    check(3'b0x0); check(3'b0z0); check(3'b100); check(3'b111);\n"
          "    check(3'b00x); check(3'b01x); check(3'bxxx);\n"
          "  end\n"
          "endmodule\n",
          f),
      "task1 001\ntask1 011\ntask2 000\ntask2 010\ntask2 0x0\ntask2 0z0\ntask2 "
      "100\ntask2 111\n");
  EXPECT_EQ(f.diag.WarningCount(), 3u);
}

TEST(CaseInsideStatementSim, TheItemsAreEvaluatedInOrderUntilTheFirstMatch) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  function automatic int note(input int v);\n"
                       "    $write(\"%0d \", v);\n"
                       "    return v;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    case (note(5)) inside\n"
                       "      note(1), [note(2):note(3)]: $display(\"low\");\n"
                       "      [note(4):note(6)], note(7): $display(\"mid\");\n"
                       "      note(8): $display(\"high\");\n"
                       "    endcase\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5 1 2 3 4 6 mid\n");
}

}  // namespace
