#include <gtest/gtest.h>

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

}  // namespace
