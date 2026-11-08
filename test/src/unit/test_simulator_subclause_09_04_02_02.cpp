#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

uint64_t RunAndReadVar(SimFixture& f, const std::string& src,
                       const char* var_name) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  if (!design) return ~0ull;
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable(var_name);
  EXPECT_NE(v, nullptr);
  return v ? v->value.ToUint64() : ~0ull;
}

TEST(ImplicitSensitivitySim, WakesOnRhsOperandChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [7:0] a, b, y;\n"
                             "  always @* y = a + b;\n"
                             "  initial begin\n"
                             "    a = 8'h01; b = 8'h02;\n"
                             "    #5 a = 8'h10;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0x12u);
}

TEST(ImplicitSensitivitySim, WakesOnSecondRhsOperandChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [7:0] a, b, y;\n"
                             "  always @* y = a + b;\n"
                             "  initial begin\n"
                             "    a = 8'h20; b = 8'h01;\n"
                             "    #5 b = 8'h05;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0x25u);
}

TEST(ImplicitSensitivitySim, WakesOnSubroutineArgChange) {
  SimFixture f;
  uint64_t y =
      RunAndReadVar(f,
                    "module t;\n"
                    "  function logic [7:0] dbl(input logic [7:0] v);\n"
                    "    return v << 1;\n"
                    "  endfunction\n"
                    "  logic [7:0] a, y;\n"
                    "  always @* y = dbl(a);\n"
                    "  initial begin\n"
                    "    a = 8'h03;\n"
                    "    #5 a = 8'h05;\n"
                    "    #5 $finish;\n"
                    "  end\n"
                    "endmodule\n",
                    "y");
  EXPECT_EQ(y, 0x0Au);
}

TEST(ImplicitSensitivitySim, WakesOnCaseSelectorChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [1:0] sel;\n"
                             "  logic [7:0] y;\n"
                             "  always @*\n"
                             "    case (sel)\n"
                             "      2'b00: y = 8'h10;\n"
                             "      2'b01: y = 8'h20;\n"
                             "      default: y = 8'hFF;\n"
                             "    endcase\n"
                             "  initial begin\n"
                             "    sel = 2'b00;\n"
                             "    #5 sel = 2'b01;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0x20u);
}

TEST(ImplicitSensitivitySim, WakesOnCaseItemExprChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [3:0] state;\n"
                             "  logic [7:0] y;\n"
                             "  always @*\n"
                             "    case (1'b1)\n"
                             "      state[0]: y = 8'h11;\n"
                             "      state[1]: y = 8'h22;\n"
                             "      state[2]: y = 8'h33;\n"
                             "      default:  y = 8'hFF;\n"
                             "    endcase\n"
                             "  initial begin\n"
                             "    state = 4'b0001;\n"
                             "    #5 state = 4'b0100;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0x33u);
}

TEST(ImplicitSensitivitySim, WakesOnConditionalSelectorChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic sel;\n"
                             "  logic [7:0] a, b, y;\n"
                             "  always @* y = sel ? a : b;\n"
                             "  initial begin\n"
                             "    a = 8'hAA; b = 8'hBB; sel = 1'b0;\n"
                             "    #5 sel = 1'b1;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0xAAu);
}

TEST(ImplicitSensitivitySim, WakesOnLhsIndexChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [1:0] idx;\n"
                             "  logic v;\n"
                             "  logic [3:0] y;\n"
                             "  always @* y[idx] = v;\n"
                             "  initial begin\n"
                             "    y = 4'b0000; v = 1'b1; idx = 2'd0;\n"
                             "    #5 idx = 2'd2;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0b0101u);
}

TEST(ImplicitSensitivitySim, WakesOnNetOperandChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic a;\n"
                             "  wire w;\n"
                             "  logic y;\n"
                             "  assign w = a;\n"
                             "  always @* y = w;\n"
                             "  initial begin\n"
                             "    a = 1'b0;\n"
                             "    #5 a = 1'b1;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 1u);
}

TEST(ImplicitSensitivitySim, ProceduralStarWaitsOnImpliedRead) {
  SimFixture f;
  uint64_t x = RunAndReadVar(f,
                             "module t;\n"
                             "  logic c = 1'b0;\n"
                             "  logic x = 1'b0;\n"
                             "  initial begin\n"
                             "    @* x = c;\n"
                             "  end\n"
                             "  initial begin\n"
                             "    #5 c = 1'b1;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "x");
  EXPECT_EQ(x, 1u);
}

TEST(ImplicitSensitivitySim, DoesNotWakeOnPureLhsWrite) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [7:0] a, y;\n"
                             "  always @* y = a;\n"
                             "  initial begin\n"
                             "    a = 8'h05;\n"
                             "    #5 y = 8'hFF;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0xFFu);
}

TEST(ImplicitSensitivitySim, ParenFormWakesLikeStar) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [7:0] a, b, y;\n"
                             "  always @(*) y = a | b;\n"
                             "  initial begin\n"
                             "    a = 8'h00; b = 8'h0F;\n"
                             "    #5 a = 8'hF0;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0xFFu);
}

TEST(ImplicitSensitivitySim, VariableIndexReadWakesOnAnElementWrite) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a[3]; int n = 0; int j = 1;\n"
                       "  always @* n = a[j] + 5;\n"
                       "  initial begin\n"
                       "    #1 a[1] = 1;\n"
                       "    #1 $display(\"n=%0d\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=6\n");
}

TEST(ImplicitSensitivitySim, TwoDimensionalVariableIndexReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a[2][3]; int n = 0; int i = 1, j = 2;\n"
                       "  always @* n = a[i][j] + 5;\n"
                       "  initial begin\n"
                       "    #1 a[1][2] = 1;\n"
                       "    #1 $display(\"n=%0d\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=6\n");
}

}  // namespace
