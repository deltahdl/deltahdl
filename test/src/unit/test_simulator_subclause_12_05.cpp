#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CaseStatementSim, CaseMultiExpressionItemMatchesAnyExpr) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case (sel)\n"
      "      8'd3, 8'd5, 8'd7: x = 8'd42;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CaseStatementSim, CaseFirstMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "      8'd2: x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseStatementSim, CaseDefaultFallthrough) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(CaseStatementSim, CaseNoDefaultNoMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    sel = 8'd5;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CaseStatementSim, CaseInsideForLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      case(i)\n"
      "        0: total = total + 8'd1;\n"
      "        1: total = total + 8'd10;\n"
      "        2: total = total + 8'd100;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 111u);
}

TEST(CaseStatementSim, NestedCaseExecution) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, x;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd1;\n"
      "    case(a)\n"
      "      8'd0: case(b)\n"
      "              8'd0: x = 8'd10;\n"
      "              8'd1: x = 8'd20;\n"
      "              default: x = 8'd30;\n"
      "            endcase\n"
      "      default: x = 8'd40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseStatementSim, CaseWithBlockBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    case(1)\n"
      "      1: begin x = 8'd5; y = 8'd6; end\n"
      "      default: begin x = 8'd0; y = 8'd0; end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 5u);
  EXPECT_EQ(y->value.ToUint64(), 6u);
}

TEST(CaseStatementSim, CaseExactXMatchesX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'bxxxxxxxx;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'bxxxxxxxx: x = 8'd20;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseStatementSim, CaseExactZMatchesZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'bzzzzzzzz;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'bzzzzzzzz: x = 8'd30;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(CaseStatementSim, CaseXDoesNotMatchZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'bxxxxxxxx;\n"
      "    x = 8'd42;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CaseStatementSim, CaseLinearSearchFirstMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(CaseStatementSim, ConstExprAsCaseExpr) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    case(1)\n"
      "      a: x = 8'd10;\n"
      "      default: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(CaseStatementSim, SequentialCaseStatements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    case(1)\n"
      "      1: x = 8'd11;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "    case(0)\n"
      "      0: y = 8'd22;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 11u);
  EXPECT_EQ(y->value.ToUint64(), 22u);
}

TEST(CaseStatementSim, ConstCaseExprPriorityEncoder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [2:0] encode;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    encode = 3'b010;\n"
      "    case (1)\n"
      "      encode[2]: x = 8'd2;\n"
      "      encode[1]: x = 8'd1;\n"
      "      encode[0]: x = 8'd0;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseStatementSim, ConstCaseExprFallsToDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [2:0] encode;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    encode = 3'b000;\n"
      "    case (1)\n"
      "      encode[2]: x = 8'd2;\n"
      "      encode[1]: x = 8'd1;\n"
      "      encode[0]: x = 8'd0;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(CaseStatementSim, AlwaysCombCaseDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [2:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 3'd7;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      3'd0: result = 8'd1;\n"
      "      3'd1: result = 8'd2;\n"
      "      default: result = 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(CaseStatementSim, AlwaysCombCaseMatch) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 8'h10;\n"
      "      2'b01: y = 8'h20;\n"
      "      2'b10: y = 8'h30;\n"
      "      default: y = 8'hFF;\n"
      "    endcase\n"
      "  initial begin\n"
      "    sel = 2'b10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

TEST(CaseStatementSim, IncompleteCaseFirstArmMatch) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] q;\n"
      "  initial sel = 2'b01;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b01: q = 8'hAA;\n"
      "      2'b10: q = 8'hBB;\n"
      "    endcase\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xAAu);
}

TEST(CaseStatementSim, IncompleteCaseSecondArm) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] q;\n"
      "  initial sel = 2'b10;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b01: q = 8'hAA;\n"
      "      2'b10: q = 8'hBB;\n"
      "    endcase\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xBBu);
}

TEST(CaseStatementSim, BlockingAssignCase) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  int result;\n"
      "  initial begin\n"
      "    sel = 2;\n"
      "    case (sel)\n"
      "      0: result = 10;\n"
      "      1: result = 20;\n"
      "      2: result = 30;\n"
      "      default: result = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(CaseStatementSim, CaseDefaultInMiddlePosition) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      default: x = 8'd99;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(CaseStatementSim, CaseAllSignedSignExtendsToLongest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [3:0] sel;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sel = -1;\n"
      "    case (sel)\n"
      "      8'sh0F: x = 8'd1;\n"
      "      8'shFF: x = 8'd2;\n"
      "      default: x = 8'd9;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(CaseStatementSim, CaseUnsignedItemForcesZeroExtend) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [3:0] sel;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sel = -1;\n"
      "    case (sel)\n"
      "      8'hFF: x = 8'd1;\n"
      "      8'h0F: x = 8'd2;\n"
      "      default: x = 8'd9;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(CaseStatementSim, CaseUnsignedWidthEqualizeToLongest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sel = 4'hF;\n"
      "    case (sel)\n"
      "      8'hFF: x = 8'd1;\n"
      "      8'h0F: x = 8'd2;\n"
      "      default: x = 8'd9;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(CaseStatementSim, CaseNullBodyItemMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    case(8'd1)\n"
      "      8'd1: ;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CaseStatementSim, CaseExpressionEvaluatedExactlyOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  int calls;\n"
      "  function logic [7:0] pick();\n"
      "    calls = calls + 1;\n"
      "    return 8'd2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    calls = 0;\n"
      "    case (pick())\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "      8'd2: x = 8'd30;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* calls = f.ctx.FindVariable("calls");
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(calls, nullptr);
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
  EXPECT_EQ(x->value.ToUint64(), 30u);
}

TEST(CaseStatementSim, CaseDefaultIgnoredDuringSearch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case (sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      default: x = 8'd99;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseStatementSim, CaseExactMatchMixedFourState) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'b1x0z_1x0z;\n"
      "    case (sel)\n"
      "      8'b1x0z_1x0x: x = 8'd1;\n"
      "      8'b1x0z_1x0z: x = 8'd2;\n"
      "      default: x = 8'd9;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(CaseStatementSim, CaseConcatItemWidthEqualizesToSelector) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'h0B;\n"
      "    case (sel)\n"
      "      8'hFB: x = 8'd1;\n"
      "      {2'b10, 2'b11}: x = 8'd2;\n"
      "      default: x = 8'd9;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(CaseStatementSim, CaseTypeDerivedSignedSelectorSignExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte sel;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sel = -1;\n"
      "    case (sel)\n"
      "      16'shFFFF: x = 8'd1;\n"
      "      16'sh00FF: x = 8'd2;\n"
      "      default: x = 8'd9;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseStatementSim, CaseExpressionEvaluatedAtTheCommonLength) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a = 4'hF, b = 4'h1;\n"
      "  int x;\n"
      "  initial case (a + b) 5'h10: x = 1; default: x = 2; endcase\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

TEST(CaseStatementSim, UnbasedUnsizedItemFillsTheCommonLength) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] s = 8'hFF;\n"
      "  int x;\n"
      "  initial case (s) '1: x = 1; 16'h1234: x = 2; default: x = 3; endcase\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 3u);
}

TEST(CaseStatementSim, UnbasedUnsizedCaseExpressionFillsTheCommonLength) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial case ('1) 8'hFF: x = 1; default: x = 2; endcase\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

TEST(CaseStatementSim, OneUnsignedItemMakesEveryExpressionUnsigned) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  logic signed [3:0] s = -1;\n"
      "  int x;\n"
      "  initial case (s) -1: x = 1; 4'd0: x = 2; default: x = 3; endcase\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 3u);
}

TEST(CaseExampleSim, TheDecoderExampleClearsOneBitPerValueAndElseX) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [15:0] data;\n"
                       "  logic [9:0] result;\n"
                       "  task decode(input logic [15:0] d);\n"
                       "    data = d;\n"
                       "    case (data)\n"
                       "      16'd0:  result = 10'b0111111111;\n"
                       "      16'd1:  result = 10'b1011111111;\n"
                       "      16'd2:  result = 10'b1101111111;\n"
                       "      16'd3:  result = 10'b1110111111;\n"
                       "      16'd4:  result = 10'b1111011111;\n"
                       "      16'd5:  result = 10'b1111101111;\n"
                       "      16'd6:  result = 10'b1111110111;\n"
                       "      16'd7:  result = 10'b1111111011;\n"
                       "      16'd8:  result = 10'b1111111101;\n"
                       "      16'd9:  result = 10'b1111111110;\n"
                       "      default result = 'x;\n"
                       "    endcase\n"
                       "    $display(\"%b\", result);\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    decode(16'd0); decode(16'd4); decode(16'd9); "
                       "decode(16'd12); decode('x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0111111111\n1111011111\n1111111110\nxxxxxxxxxx\nxxxxxxxxxx\n");
}

TEST(CaseExampleSim, TheXAndZExampleResolvesAnUnknownSelectBit) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  logic [1:2] select;\n"
          "  logic flaga, flagb, result;\n"
          "  task pick(input logic [1:2] s, input logic fa, input logic fb);\n"
          "    select = s; flaga = fa; flagb = fb;\n"
          "    case (select[1:2])\n"
          "      2'b00:  result = 0;\n"
          "      2'b01:  result = flaga;\n"
          "      2'b0x,\n"
          "      2'b0z:  result = flaga ? 'x : 0;\n"
          "      2'b10:  result = flagb;\n"
          "      2'bx0,\n"
          "      2'bz0:  result = flagb ? 'x : 0;\n"
          "      default result = 'x;\n"
          "    endcase\n"
          "    $display(\"%b\", result);\n"
          "  endtask\n"
          "  initial begin\n"
          "    pick(2'b0x, 0, 1); pick(2'b0z, 1, 0); pick(2'b01, 1, 0); "
          "pick(2'b10, 0, 1);\n"
          "    pick(2'bx0, 0, 1); pick(2'bz0, 1, 0); pick(2'b11, 0, 0); "
          "pick(2'b00, 1, 1);\n"
          "  end\n"
          "endmodule\n",
          f),
      "0\nx\n1\n1\nx\n0\nx\n0\n");
}

TEST(CaseExampleSim, TheSignalExampleTellsFloatingFromUnknown) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  logic sig;\n"
                 "  task show(input logic s);\n"
                 "    sig = s;\n"
                 "    case (sig)\n"
                 "      1'bz:    $display(\"signal is floating\");\n"
                 "      1'bx:    $display(\"signal is unknown\");\n"
                 "      default: $display(\"signal is %b\", sig);\n"
                 "    endcase\n"
                 "  endtask\n"
                 "  initial begin\n"
                 "    show(1'bz); show(1'bx); show(1'b1); show(1'b0);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "signal is floating\nsignal is unknown\nsignal is 1\nsignal is 0\n");
}

TEST(CaseStatementSim, TheItemsAreEvaluatedInOrderUntilTheFirstMatch) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  function automatic int note(input int v);\n"
                       "    $write(\"%0d \", v);\n"
                       "    return v;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    case (note(2))\n"
                       "      note(1): $display(\"one\");\n"
                       "      note(2), note(3): $display(\"two\");\n"
                       "      note(2): $display(\"again\");\n"
                       "      default: $display(\"none\");\n"
                       "    endcase\n"
                       "    case (note(9))\n"
                       "      note(7): $display(\"seven\");\n"
                       "      default: $display(\"default\");\n"
                       "      note(8): $display(\"eight\");\n"
                       "    endcase\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 1 2 two\n9 7 8 default\n");
}

TEST(CaseStatementSim, EveryKindOfCaseDecidesInEveryKindOfProcedure) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  function automatic int f(input logic [3:0] v);\n"
                       "    casez (v)\n"
                       "      4'b1???: return 1;\n"
                       "      default return 0;\n"
                       "    endcase\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "function automatic int g(input logic [3:0] v);\n"
                       "  casex (v)\n"
                       "    4'b01xx: return 2;\n"
                       "    default: return 0;\n"
                       "  endcase\n"
                       "endfunction\n"
                       "class C;\n"
                       "  function int m(input int v);\n"
                       "    case (v) inside\n"
                       "      [1:3]: return 3;\n"
                       "      default: return 0;\n"
                       "    endcase\n"
                       "  endfunction\n"
                       "endclass\n"
                       "interface I;\n"
                       "  logic [1:0] v;\n"
                       "  initial begin\n"
                       "    v = 2'bz1;\n"
                       "    #2 case (v)\n"
                       "      2'b01: $display(\"I 01\");\n"
                       "      2'bz1: $display(\"I z1\");\n"
                       "      default: $display(\"I other\");\n"
                       "    endcase\n"
                       "  end\n"
                       "endinterface\n"
                       "program p;\n"
                       "  initial #3 unique case (2)\n"
                       "    1: $display(\"P one\");\n"
                       "    2: $display(\"P two\");\n"
                       "  endcase\n"
                       "endprogram\n"
                       "module t;\n"
                       "  I u();\n"
                       "  p pp();\n"
                       "  task tk(input int v);\n"
                       "    priority case (v)\n"
                       "      0: $display(\"T zero\");\n"
                       "      1, 2: $display(\"T low\");\n"
                       "    endcase\n"
                       "  endtask\n"
                       "  if (1) begin : gb\n"
                       "    initial #1 casez (4'b10z1)\n"
                       "      4'b11?1: $display(\"G one\");\n"
                       "      4'b10?1: $display(\"G hit\");\n"
                       "      default: $display(\"G miss\");\n"
                       "    endcase\n"
                       "  end\n"
                       "  initial begin\n"
                       "    C c;\n"
                       "    c = new;\n"
                       "    $display(\"%0d %0d %0d %0d\", pk::f(4'b1010), "
                       "g(4'b01z1), c.m(2), c.m(5));\n"
                       "    tk(2);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 2 3 0\nT low\nG hit\nI z1\nP two\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
