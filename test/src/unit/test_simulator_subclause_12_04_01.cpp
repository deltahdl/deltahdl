#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ConditionalStatementSim, IfElseIfChainSelectsCorrectBranch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd2;\n"
      "    if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else if (a == 8'd2) x = 8'd30;\n"
      "    else x = 8'd40;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(ConditionalStatementSim, DeepIfElseIfLastElseTaken) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (0) x = 8'd1;\n"
      "    else if (0) x = 8'd2;\n"
      "    else if (0) x = 8'd3;\n"
      "    else x = 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(ConditionalStatementSim, IfElseIfFirstConditionTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(ConditionalStatementSim, IfElseIfBlockBodyFirstMatchTerminatesChain) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      x = 8'd11;\n"
      "      y = 8'd22;\n"
      "    end else if (1) begin\n"
      "      x = 8'd33;\n"
      "      y = 8'd44;\n"
      "    end else begin\n"
      "      x = 8'd55;\n"
      "      y = 8'd66;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  auto* yv = f.ctx.FindVariable("y");
  ASSERT_NE(xv, nullptr);
  ASSERT_NE(yv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 11u);
  EXPECT_EQ(yv->value.ToUint64(), 22u);
}

TEST(ConditionalStatementSim, IfElseIfBlockBodyDefaultElseExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd0; y = 8'd0;\n"
      "    if (0) begin x = 8'd1; y = 8'd2; end\n"
      "    else if (0) begin x = 8'd3; y = 8'd4; end\n"
      "    else begin x = 8'd55; y = 8'd66; end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  auto* yv = f.ctx.FindVariable("y");
  ASSERT_NE(xv, nullptr);
  ASSERT_NE(yv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 55u);
  EXPECT_EQ(yv->value.ToUint64(), 66u);
}

TEST(ConditionalStatementSim, IfElseIfFirstTrueSkipsLaterConditionSideEffect) {
  SimFixture f;
  auto [x, i] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  logic [7:0] x, i;\n"
                                 "  initial begin\n"
                                 "    i = 8'd0;\n"
                                 "    if (1) x = 8'd10;\n"
                                 "    else if (i++ < 8'd5) x = 8'd20;\n"
                                 "    else x = 8'd30;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "i");
  EXPECT_EQ(x, 10u);
  EXPECT_EQ(i, 0u);
}

TEST(ConditionalStatementSim,
     IfElseIfEarlierConditionSideEffectAppliedInOrder) {
  SimFixture f;
  auto [x, i] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  logic [7:0] x, i;\n"
                                 "  initial begin\n"
                                 "    i = 8'd0;\n"
                                 "    if (i++ == 8'd9) x = 8'd10;\n"
                                 "    else if (i == 8'd1) x = 8'd20;\n"
                                 "    else x = 8'd30;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "i");
  EXPECT_EQ(x, 20u);
  EXPECT_EQ(i, 1u);
}

TEST(ConditionalStatementSim, IfElseIfUnknownConditionSkippedContinuesInOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic cond;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    if (cond) x = 8'd10;\n"
      "    else if (1'b1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(ConditionalStatementSim, IfElseIfNoMatchNoElseRetainsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd77;\n"
      "    if (0) x = 8'd10;\n"
      "    else if (0) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(IfElseIfExampleSim, TheIndexExampleTakesTheBranchOfTheFirstTrueCondition) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  logic [31:0] instruction, segment_area[255:0];\n"
                 "  logic [7:0] index;\n"
                 "  logic [5:0] modify_seg1, modify_seg2, modify_seg3;\n"
                 "  parameter segment1 = 0, inc_seg1 = 1, segment2 = 20, "
                 "inc_seg2 = 2,\n"
                 "            segment3 = 64, inc_seg3 = 4, data = 128;\n"
                 "  task step(input logic [7:0] start);\n"
                 "    index = start;\n"
                 "    if (index < segment2) begin\n"
                 "      instruction = segment_area [index + modify_seg1];\n"
                 "      index = index + inc_seg1;\n"
                 "    end\n"
                 "    else if (index < segment3) begin\n"
                 "      instruction = segment_area [index + modify_seg2];\n"
                 "      index = index + inc_seg2;\n"
                 "    end\n"
                 "    else if (index < data) begin\n"
                 "      instruction = segment_area [index + modify_seg3];\n"
                 "      index = index + inc_seg3;\n"
                 "    end\n"
                 "    else\n"
                 "      instruction = segment_area [index];\n"
                 "    $display(\"%0d %0d\", instruction, index);\n"
                 "  endtask\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 256; i++) segment_area[i] = i * 3;\n"
                 "    modify_seg1 = 2; modify_seg2 = 3; modify_seg3 = 5;\n"
                 "    step(5); step(30); step(100); step(200);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "21 6\n99 32\n315 104\n600 200\n");
}

}  // namespace
