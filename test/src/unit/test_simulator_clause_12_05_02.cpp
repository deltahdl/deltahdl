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

}  // namespace
