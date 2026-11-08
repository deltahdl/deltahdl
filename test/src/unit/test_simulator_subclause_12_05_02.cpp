#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ConstExprCaseSim, ConstantCompiledAgainstBitSelectItems) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "line");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ConstExprCaseSim, ConstantWithNoMatchingItemTakesDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "line");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ConstExprCaseSim, ConstantTakesFirstMatchingItem) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "line");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(ConstExprCaseSim, CompoundConstantExpressionAsCaseExpr) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "line");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(ConstExprCaseSim, ParameterAsCaseExpr) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "line");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(ConstExprCaseSim, LocalparamAsCaseExpr) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "line");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(ConstExprCaseSim, ConstantFunctionCallAsCaseExpr) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "line");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(ConstExprCaseSim, GenvarAsCaseExpr) {
  SimFixture f;
  RunModuleArray(f,
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
                 "out", {10u, 20u, 30u, 99u});
}

}  // namespace
