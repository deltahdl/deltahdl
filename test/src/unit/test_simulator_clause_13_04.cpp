#include "helpers_scheduler.h"

using namespace delta;

namespace {

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

// §13.4 p.341 argument-direction table: an inout formal copies the actual's
// value in at the start of the call and copies the formal's value back out at
// the end. Reading the incoming value (41) and writing an updated value back
// exercises both halves — a missing copy-in would start from the default and a
// missing copy-out would leave x at 41, so x==42 discriminates both. Input
// (copy-in) and output (copy-out) are already observed by FunctionWithLocalVars
// and FunctionMultipleStatements; this closes the remaining inout input form.
TEST(FunctionSim, FunctionInoutArgCopiesInAndOut) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void bump(inout logic [7:0] v);\n"
      "    v = v + 8'd1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd41;\n"
      "    bump(x);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
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
