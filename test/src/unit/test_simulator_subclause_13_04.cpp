#include <gtest/gtest.h>

#include "fixture_simulator.h"
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

TEST(FunctionSim, OldStyleInputWithAPackedRangeAloneHasItsWidth) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  function [15:0] inc;\n"
      "    input [7:0] a;\n"
      "    inc = a + 16'd1;\n"
      "  endfunction\n"
      "  initial x = inc(16'h01FF);\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0x100u);
}

TEST(FunctionSim, OldStyleSignedInputWithAPackedRangeIsSignedLogic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  function [15:0] ext;\n"
      "    input signed [7:0] a;\n"
      "    ext = a;\n"
      "  endfunction\n"
      "  initial x = ext(16'h01FF);\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0xFFFFu);
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

TEST(FunctionSim, TypedefNameLocalIsSizedByTheTypeItNames) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] f();\n"
      "    static nib v = 8'hFF;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 15u);
}

TEST(FunctionSim, TypedefNameLocalWiderThanOneWordKeepsItsHighBits) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef bit [39:0] wide;\n"
      "  logic [63:0] x;\n"
      "  function logic [63:0] f();\n"
      "    static wide v = 48'hFFFF00000001;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 1095216660481ull);
}

TEST(FunctionSim, DeclaredLocalInitializedFromAVariableGetsItsOwnWords) {
  SimFixture f;
  auto* source = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] held;\n"
      "  bit [7:0] seen;\n"
      "  function bit [7:0] note(bit [7:0] arg);\n"
      "    return arg;\n"
      "  endfunction\n"
      "  function automatic void relay();\n"
      "    logic [7:0] mirror = held;\n"
      "    seen = note(mirror);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    held = 8'b0x1110x0;\n"
      "    relay();\n"
      "  end\n"
      "endmodule\n",
      f, "held");
  ASSERT_NE(source, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* noted = f.ctx.FindVariable("seen");
  ASSERT_NE(noted, nullptr);
  EXPECT_EQ(source->value.words[0].aval & 0xFFu, 0x7Au);
  EXPECT_EQ(source->value.words[0].bval & 0xFFu, 0x42u);
  EXPECT_EQ(noted->value.words[0].aval & 0xFFu, 0x38u);
  EXPECT_EQ(noted->value.words[0].bval & 0xFFu, 0x00u);
}

TEST(FunctionSim, DeclaredLocalInitializedFromAnElementGetsItsOwnWords) {
  SimFixture f;
  auto* element = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] bank [0:1];\n"
      "  bit [7:0] taken;\n"
      "  function bit [7:0] echo_bits(bit [7:0] bits_in);\n"
      "    return bits_in;\n"
      "  endfunction\n"
      "  function automatic void lift();\n"
      "    logic [7:0] slot = bank[1];\n"
      "    taken = echo_bits(slot);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    bank[1] = 8'b1zz01x10;\n"
      "    lift();\n"
      "  end\n"
      "endmodule\n",
      f, "bank[1]");
  ASSERT_NE(element, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* lifted = f.ctx.FindVariable("taken");
  ASSERT_NE(lifted, nullptr);
  EXPECT_EQ(element->value.words[0].aval & 0xFFu, 0x8Eu);
  EXPECT_EQ(element->value.words[0].bval & 0xFFu, 0x64u);
  EXPECT_EQ(lifted->value.words[0].aval & 0xFFu, 0x8Au);
  EXPECT_EQ(lifted->value.words[0].bval & 0xFFu, 0x00u);
}

TEST(FunctionSim, CaseStatementInFunctionAndMethodBodies) {
  auto val = RunAndGet(
      "class C;\n"
      "  int kind = 2;\n"
      "  function int tens();\n"
      "    case (kind)\n"
      "      1: tens = 10;\n"
      "      2: tens = 20;\n"
      "      default: tens = 90;\n"
      "    endcase\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  function int units(int k);\n"
      "    case (k)\n"
      "      1: units = 1;\n"
      "      2: units = 2;\n"
      "      default: units = 9;\n"
      "    endcase\n"
      "  endfunction\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    r = o.tens() + units(1) + 100 * units(7);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 921u);
}

TEST(FunctionSim, GenerateBlockFunctionCalledByHierarchicalName) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      function int triple(int x); return x * 3; endfunction\n"
      "      initial if (g == 1) r = triple(10);\n"
      "    end\n"
      "  endgenerate\n"
      "  initial #1 r = r + 100 * blk[1].triple(10);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3030u);
}

TEST(FunctionSim, GenerateBlockFunctionReadsItsOwnInstanceLoopIndex) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      function int scaled(int x); return x * (g + 2); endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "  initial r = blk[0].scaled(10) + 100 * blk[1].scaled(10);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3020u);
}

TEST(FunctionSim, GenerateBlockFunctionReadsTheBlockInstancesOwnVariable) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      int base;\n"
      "      initial base = 100 * g;\n"
      "      function int addbase(int x); return x + base; endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "  initial #1 r = blk[1].addbase(5);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 105u);
}

TEST(FunctionSim, GenerateBlockFunctionActualReadsTheCallersBlock) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      int base;\n"
      "      initial base = g == 0 ? 7 : 100;\n"
      "      function int addbase(int x); return x + base; endfunction\n"
      "      initial if (g == 0) #1 r = blk[1].addbase(base);\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 107u);
}

TEST(FunctionSim, ConditionalGenerateBlockFunctionCalledByHierarchicalName) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  generate\n"
      "    if (1) begin : g1\n"
      "      function int quad(int x); return x * 4; endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "  initial r = g1.quad(10);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 40u);
}

TEST(FunctionSim, GenerateBlockTaskEnabledByHierarchicalName) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      task tk(int d); #d r = r + g + 10; endtask\n"
      "    end\n"
      "  endgenerate\n"
      "  initial blk[1].tk(2);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 11u);
}

TEST(FunctionSim, GenerateBlockFunctionOfAChildInstance) {
  auto val = RunAndGet(
      "module sub;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      function int scaled(int x); return x * (g + 2); endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n"
      "module t;\n"
      "  int r;\n"
      "  sub u1();\n"
      "  initial r = u1.blk[1].scaled(10);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 30u);
}

TEST(FunctionSim, GenerateBlockFunctionOfAParallelTop) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "module m;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      function int scaled(int x); return x * (g + 2); endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n"
      "module n;\n"
      "  int r;\n"
      "  initial r = m.blk[1].scaled(10);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"n.r", 30u}});
}

TEST(FunctionSim, OldStylePortAfterABodyDeclaration) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  function int f;\n"
      "    input int a;\n"
      "    int s;\n"
      "    input int b;\n"
      "    s = a;\n"
      "    f = s + b;\n"
      "  endfunction\n"
      "  initial r = f(5, 9);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 14u);
}

TEST(FunctionSim, BodyDeclarationTypesADirectionOnlyFormal) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  function int g;\n"
      "    input a;\n"
      "    int a;\n"
      "    g = a;\n"
      "  endfunction\n"
      "  initial r = g(5);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 5u);
}

}  // namespace
