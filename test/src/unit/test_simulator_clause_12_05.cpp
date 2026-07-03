#include <string_view>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §12.5: a case item may list several expressions separated by commas; the
// selector matches the item when it equals any one of them. Here the middle
// expression of the list is the matching one, driven end to end from source.
TEST(CaseStatementSim, CaseMultiExpressionItemMatchesAnyExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CaseStatementSim, CaseFirstMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseStatementSim, CaseDefaultFallthrough) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(CaseStatementSim, CaseNoDefaultNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CaseStatementSim, CaseInsideForLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 111u);
}

TEST(CaseStatementSim, NestedCaseExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CaseStatementSim, CaseExactZMatchesZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(CaseStatementSim, CaseXDoesNotMatchZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CaseStatementSim, CaseLinearSearchFirstMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(CaseStatementSim, ConstExprAsCaseExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CaseStatementSim, ConstCaseExprFallsToDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(CaseStatementSim, AlwaysCombCaseDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(CaseStatementSim, AlwaysCombCaseMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

TEST(CaseStatementSim, IncompleteCaseFirstArmMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xAAu);
}

TEST(CaseStatementSim, IncompleteCaseSecondArm) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xBBu);
}

TEST(CaseStatementSim, BlockingAssignCase) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(CaseStatementSim, CaseEmptyNoItems) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    case(x) endcase\n"
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

TEST(CaseStatementSim, CaseDefaultInMiddlePosition) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §12.5: all case expressions are made equal to the length of the longest, and
// when every expression is signed the shorter ones are sign-extended. A 4-bit
// signed selector holding -1 must therefore match the 8-bit signed pattern that
// also denotes -1, not the 8-bit pattern whose low nibble happens to agree.
TEST(CaseStatementSim, CaseAllSignedSignExtendsToLongest) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.5: if any of the case expressions is unsigned, all of them are treated as
// unsigned. So even though the selector is declared signed, the presence of
// unsigned item expressions forces a zero-extended comparison: -1 in 4 bits
// widens to 0x0F, matching the unsigned 8'h0F pattern rather than 8'hFF.
TEST(CaseStatementSim, CaseUnsignedItemForcesZeroExtend) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.5: the length equalization also governs a plain unsigned comparison. A
// 4-bit selector holding 0xF is widened to the 8-bit item length, so it matches
// 8'h0F and does not match 8'hFF -- a comparison that only looked at the low
// nibble would wrongly match 8'hFF.
TEST(CaseStatementSim, CaseUnsignedWidthEqualizeToLongest) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(CaseStatementSim, CaseNullBodyItemMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §12.5: the case expression is evaluated exactly once, before any of the item
// expressions. A function whose side effect counts its own invocations is used
// as the case expression; after the statement runs the counter must read 1 (an
// implementation that re-evaluated the expression per item comparison would
// leave it at the number of items scanned).
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

// §12.5: a default item is ignored during the linear search. Here the default
// sits ahead of a matching item in the list, yet the search must skip it and
// execute the later matching item, not the default.
TEST(CaseStatementSim, CaseDefaultIgnoredDuringSearch) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.5: a plain-case comparison is exact for every bit with respect to 0, 1,
// x, and z. This drives a heterogeneous selector that mixes all four values and
// requires the matching item to agree in every position; a pattern that differs
// only in a single z-versus-x bit must not match.
TEST(CaseStatementSim, CaseExactMatchMixedFourState) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.5 (width equalization, consuming the §11.6.1 concatenation width): a case
// item may be any expression, including a concatenation whose length is fixed
// by the bit-length rules. The 4-bit concatenation is widened to the 8-bit
// selector length, so 0xB matches 0x0B and does not match 0xFB.
TEST(CaseStatementSim, CaseConcatItemWidthEqualizesToSelector) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.5 (sign treatment, consuming §11.8.1 signedness): signedness can come
// from the operand's type, not just an explicit `signed` keyword. A `byte`
// selector is signed, and with all-signed item expressions the shorter selector
// is sign-extended to the 16-bit item length, so -1 matches 16'shFFFF rather
// than the same low byte 16'sh00FF.
TEST(CaseStatementSim, CaseTypeDerivedSignedSelectorSignExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
