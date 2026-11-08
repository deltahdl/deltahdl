#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ConstantFunctionSim, Clogb2ResultReachesRuntime) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function integer clogb2(input int value);\n"
      "    value = value - 1;\n"
      "    for (clogb2 = 0; value > 0; clogb2 = clogb2 + 1)\n"
      "      value = value >> 1;\n"
      "  endfunction\n"
      "  localparam addr_width = clogb2(256);\n"
      "  initial $display(\"%0d\", addr_width);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "8\n");
}

TEST(ConstantFunctionSim, FoldedValueSizesRuntimeSignal) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function int double_val(int n); return n * 2; endfunction\n"
      "  localparam int P = double_val(4);\n"
      "  logic [P-1:0] bus;\n"
      "  initial $display(\"%0d %0d\", P, $bits(bus));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "8 8\n");
}

TEST(ConstantFunctionSim, ConstFunctionCallInPackedDimension) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  logic [calc(3)-1:0] bus;\n"
      "  initial $display(\"%0d\", $bits(bus));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "6\n");
}

TEST(ConstantFunctionSim, SystemTaskInBodyProducesNoOutput) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  function int compute(int n);\n"
      "    $write(\"SIDEEFFECT\");\n"
      "    return n * 2;\n"
      "  endfunction\n"
      "  localparam int P = compute(4);\n"
      "  initial $display(\"%0d\", P);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "8\n");
}

}  // namespace
