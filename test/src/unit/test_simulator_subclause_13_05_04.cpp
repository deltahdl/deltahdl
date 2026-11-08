#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(SubroutineCallSim, NamedArgCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] sub(input logic [7:0] a, input logic [7:0] b);\n"
      "    return a - b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = sub(.b(8'd3), .a(8'd10));\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(SubroutineCallSim, MixedPositionalNamedArgs) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add3(input logic [7:0] a, input logic [7:0] b,\n"
      "                            input logic [7:0] c);\n"
      "    return a + b + c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = add3(8'd1, 8'd2, .c(8'd3));\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(SubroutineCallSim, NamedArgsOmitDefaultedArg) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] scale(input logic [7:0] val,\n"
      "                             input logic [7:0] factor = 8'd3);\n"
      "    return val * factor;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = scale(.val(8'd7));\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 21u);
}

TEST(SubroutineCallSim, NamedArgTaskOutputWriteback) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  task swap(input logic [7:0] x, input logic [7:0] y,\n"
      "            output logic [7:0] ox, output logic [7:0] oy);\n"
      "    ox = y;\n"
      "    oy = x;\n"
      "  endtask\n"
      "  initial begin\n"
      "    swap(.y(8'd20), .x(8'd10), .oy(b), .ox(a));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 20u);
  EXPECT_EQ(vb->value.ToUint64(), 10u);
}

TEST(SubroutineCallSim, EmptyNamedBindingUsesDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] scale(input logic [7:0] val = 8'd5,\n"
      "                             input logic [7:0] factor = 8'd3);\n"
      "    return val * factor;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = scale(.factor(), .val());\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(SubroutineCallSim, NamedArgBindsStringOperand) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  function int pick(int j, string s);\n"
      "    if (s == \"yes\") return j;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r = pick(.s(\"yes\"), .j(7));\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

}  // namespace
