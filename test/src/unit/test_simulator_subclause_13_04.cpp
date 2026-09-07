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

// §6.18: a variable declared with a user-defined type name is an object of the
// type that name stands for, so the `nib v` of a function body is four bits
// wide, and §6.8 makes the declaration's initializer an assignment into it, so
// §10.7 truncates 8'hFF to 15 on the way in. A local the simulator could not
// size took a 32-bit carrier instead, and an initializer that replaced the
// vector rather than being assigned into it read 255. The typedef has to be
// narrower than that carrier for the two answers to differ, which is why it is
// not the `logic [31:0] tmp` of FunctionWithLocalVars.
//
// The value is written as the declaration's initializer rather than by a
// following `v = 8'hFF;` so that what is claimed is the declaration, which
// establishes the width, and not the assignment, which truncates to a width
// already established. test_simulator_subclause_10_07.cpp claims the
// assignment, on a target whose width no declaration of a typedef name is
// involved in.
TEST(FunctionSim, TypedefNameLocalIsSizedByTheTypeItNames) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] f();\n"
      "    nib v = 8'hFF;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 15u);
}

// The case above cannot say a local wider than the carrier keeps its width:
// clamping every local to 32 bits would truncate 8'hFF to 15 as well. Forty
// bits spans two words, and the three answers separate -- 48'hFFFF00000001 kept
// whole reads 281470681743361, clamped to 32 bits reads 1, and held in the
// forty bits `wide` declares reads 1095216660481, whose set bits above the
// first word are what say the high word survived.
TEST(FunctionSim, TypedefNameLocalWiderThanOneWordKeepsItsHighBits) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef bit [39:0] wide;\n"
      "  logic [63:0] x;\n"
      "  function logic [63:0] f();\n"
      "    wide v = 48'hFFFF00000001;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 1095216660481ull);
}

}  // namespace
