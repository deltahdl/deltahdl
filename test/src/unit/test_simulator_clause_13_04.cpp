#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(FunctionSim, FunctionWithOutputArg) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void set_val(output logic [31:0] v);\n"
      "    v = 32'd55;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    set_val(x);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 55u);
}

TEST(FunctionSim, FunctionWithInoutArg) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void double_it(inout logic [31:0] v);\n"
      "    v = v * 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 32'd8;\n"
      "    double_it(x);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 16u);
}

TEST(FunctionSim, FunctionWithMultipleOutputArgs) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] lo, hi;\n"
      "  function void split(input logic [31:0] v,\n"
      "                      output logic [31:0] a, b);\n"
      "    a = v & 32'hFFFF;\n"
      "    b = (v >> 16) & 32'hFFFF;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    split(32'h0005_0003, lo, hi);\n"
      "  end\n"
      "endmodule\n",
      "lo");
  EXPECT_EQ(val, 3u);
}

TEST(FunctionSim, FunctionWithLocalVars) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] compute(input logic [31:0] a,\n"
      "                                input logic [31:0] b);\n"
      "    logic [31:0] tmp;\n"
      "    tmp = a + b;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = compute(32'd10, 32'd20);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 30u);
}

TEST(FunctionSim, FunctionCallsFunction) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] add(input logic [31:0] a,\n"
      "                            input logic [31:0] b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  function logic [31:0] add3(input logic [31:0] a,\n"
      "                             input logic [31:0] b,\n"
      "                             input logic [31:0] c);\n"
      "    return add(add(a, b), c);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = add3(32'd1, 32'd2, 32'd3);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 6u);
}

TEST(FunctionSim, FunctionEmptyBody) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void nop();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 32'd5;\n"
      "    nop();\n"
      "    x = x + 32'd1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 6u);
}

TEST(FunctionSim, FunctionMultipleStatements) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void multi(output logic [31:0] v);\n"
      "    v = 32'd1;\n"
      "    v = v + 32'd2;\n"
      "    v = v + 32'd3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    multi(x);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 6u);
}

}  // namespace
