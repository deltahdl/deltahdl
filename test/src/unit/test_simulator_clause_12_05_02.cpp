// Canonical tests for IEEE 1800-2023 §12.5.2 "Constant expression in case
// statement".
//
// §12.5.2 carries no BNF of its own (the case grammar, Syntax 12-3, is
// borrowed from A.6.7 and owned by §12.5). Its sole normative requirement is a
// simulator-stage rule: a constant expression may serve as the case_expression,
// and the value of that constant shall be compared against the
// case_item_expressions. The general case-matching machinery in the simulator
// (ExecCase evaluates the case_expression once, then matches each
// case_item_expression against it) already applies this rule regardless of
// which side is constant, so these tests observe that behavior on the
// 3-bit priority-encoder shape from the LRM example.

#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// case_expression is the constant 1; the case_items are bit-select
// expressions. The first item whose value equals the constant is taken.
TEST(ConstExprCaseSim, ConstantCompiledAgainstBitSelectItems) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] encode;\n"
      "  logic [7:0] line;\n"
      "  initial begin\n"
      "    encode = 3'b010;\n"
      "    case (1)\n"
      "      encode[2]: line = 8'd2;\n"
      "      encode[1]: line = 8'd1;\n"
      "      encode[0]: line = 8'd0;\n"
      "      default:   line = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("line");
  ASSERT_NE(var, nullptr);
  // Only encode[1] is set, so the constant 1 matches the second item.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// When no case_item_expression evaluates to the constant case_expression, the
// comparison falls through to the default item.
TEST(ConstExprCaseSim, ConstantWithNoMatchingItemTakesDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] encode;\n"
      "  logic [7:0] line;\n"
      "  initial begin\n"
      "    encode = 3'b000;\n"
      "    case (1)\n"
      "      encode[2]: line = 8'd2;\n"
      "      encode[1]: line = 8'd1;\n"
      "      encode[0]: line = 8'd0;\n"
      "      default:   line = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("line");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// The constant is compared against each case_item in source order: the highest
// priority (first) matching item wins even when several bits are set.
TEST(ConstExprCaseSim, ConstantTakesFirstMatchingItem) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] encode;\n"
      "  logic [7:0] line;\n"
      "  initial begin\n"
      "    encode = 3'b111;\n"
      "    case (1)\n"
      "      encode[2]: line = 8'd2;\n"
      "      encode[1]: line = 8'd1;\n"
      "      encode[0]: line = 8'd0;\n"
      "      default:   line = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("line");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// The case_expression need not be a bare literal: any constant expression may
// be used, and its evaluated value is what gets compared against the
// case_item_expressions. Here the constant expression 1+1 is matched against
// item expressions, and the item whose value equals 2 is taken.
TEST(ConstExprCaseSim, CompoundConstantExpressionAsCaseExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, line;\n"
      "  initial begin\n"
      "    sel = 8'd2;\n"
      "    case (1 + 1)\n"
      "      sel - 8'd1: line = 8'd10;\n"
      "      sel:        line = 8'd20;\n"
      "      default:    line = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("line");
  ASSERT_NE(var, nullptr);
  // 1+1 == 2 == sel, so the second item is taken; sel-1 == 1 does not match.
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.5.2 admits any constant expression as the case_expression, not only a
// literal. §11.2.1 enumerates the constant forms; a named parameter is one of
// them. Here the constant is produced by parameter elaboration rather than a
// literal token, and its value (2) is what gets compared against the
// case_item_expressions, selecting the item equal to sel.
TEST(ConstExprCaseSim, ParameterAsCaseExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 2;\n"
      "  logic [7:0] sel, line;\n"
      "  initial begin\n"
      "    sel = 8'd2;\n"
      "    case (P)\n"
      "      sel - 8'd1: line = 8'd10;\n"
      "      sel:        line = 8'd20;\n"
      "      default:    line = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("line");
  ASSERT_NE(var, nullptr);
  // P == 2 == sel, so the second item is taken; sel-1 == 1 does not match.
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// A localparam is another §11.2.1 constant form usable as the case_expression.
// The distinct value (1) matched here comes from a localparam declaration and
// selects the first item (sel-1), confirming the localparam's value drives the
// comparison against the case_item_expressions.
TEST(ConstExprCaseSim, LocalparamAsCaseExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam LP = 1;\n"
      "  logic [7:0] sel, line;\n"
      "  initial begin\n"
      "    sel = 8'd2;\n"
      "    case (LP)\n"
      "      sel - 8'd1: line = 8'd10;\n"
      "      sel:        line = 8'd20;\n"
      "      default:    line = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("line");
  ASSERT_NE(var, nullptr);
  // LP == 1 == sel-1, so the first item is taken.
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// A constant function call is the last §11.2.1 constant form. The value the
// function returns (0) is the case_expression value compared against the
// case_item_expressions; here it selects the item equal to sel-2, showing the
// call result — not a literal — drives the match.
TEST(ConstExprCaseSim, ConstantFunctionCallAsCaseExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function automatic logic [7:0] zero();\n"
      "    zero = 8'd0;\n"
      "  endfunction\n"
      "  logic [7:0] sel, line;\n"
      "  initial begin\n"
      "    sel = 8'd2;\n"
      "    case (zero())\n"
      "      sel - 8'd2: line = 8'd5;\n"
      "      sel - 8'd1: line = 8'd10;\n"
      "      sel:        line = 8'd20;\n"
      "      default:    line = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("line");
  ASSERT_NE(var, nullptr);
  // zero() == 0 == sel-2, so the first item is taken.
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// A genvar is the remaining §11.2.1 constant form the rule admits: inside a
// loop generate the genvar is a constant expression, so it may serve as the
// case_expression. This end-to-end test builds the constant from real
// generate/genvar syntax (the §27.4 loop-generate dependency) and drives it
// through the full pipeline. Each unrolled iteration runs case (i) against
// literal case_item_expressions; the genvar's per-iteration value selects the
// matching item, and the last iteration (i == 3) has no match and takes the
// default. The selected assignment is observed via the module-level array.
TEST(ConstExprCaseSim, GenvarAsCaseExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] out [0:3];\n"
      "  generate\n"
      "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
      "      initial begin\n"
      "        case (i)\n"
      "          0: out[i] = 8'd10;\n"
      "          1: out[i] = 8'd20;\n"
      "          2: out[i] = 8'd30;\n"
      "          default: out[i] = 8'd99;\n"
      "        endcase\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // The genvar constant of each iteration matches the like-valued item; i == 3
  // matches nothing and falls through to default.
  auto* e0 = f.ctx.FindVariable("out[0]");
  auto* e1 = f.ctx.FindVariable("out[1]");
  auto* e2 = f.ctx.FindVariable("out[2]");
  auto* e3 = f.ctx.FindVariable("out[3]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  ASSERT_NE(e3, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 10u);
  EXPECT_EQ(e1->value.ToUint64(), 20u);
  EXPECT_EQ(e2->value.ToUint64(), 30u);
  EXPECT_EQ(e3->value.ToUint64(), 99u);
}

}  // namespace
