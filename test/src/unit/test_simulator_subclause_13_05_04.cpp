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

TEST(SubroutineCallSim, TheClauseFunExampleBindsEachCallAsItsPositionalForm) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  function int fun( int j = 1, string s = \"no\" );\n"
                       "    $display(\"%0d %s\", j, s);\n"
                       "    return j;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    void'(fun( .j(2), .s(\"yes\") ));\n"
                       "    void'(fun( .s(\"yes\") ));\n"
                       "    void'(fun( , \"yes\" ));\n"
                       "    void'(fun( .j(2) ));\n"
                       "    void'(fun( .s(\"yes\"), .j(2) ));\n"
                       "    void'(fun( .s(), .j() ));\n"
                       "    void'(fun( 2 ));\n"
                       "    void'(fun( ));\n"
                       "    void'(fun(2, .s(\"yes\")));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 yes\n1 yes\n1 yes\n2 no\n2 yes\n1 no\n2 no\n1 no\n2 yes\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SubroutineCallSim, NamedBindingReachesTasksMethodsAndPackageFunctions) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk;\n"
                 "  function automatic int pf(int a, int b = 4);\n"
                 "    return a * 10 + b;\n"
                 "  endfunction\n"
                 "endpackage\n"
                 "class C;\n"
                 "  function int me(int a, int b = 5);\n"
                 "    return a * 10 + b;\n"
                 "  endfunction\n"
                 "endclass\n"
                 "interface ifc;\n"
                 "  function automatic int iff_(int a, int b = 6);\n"
                 "    return a * 10 + b;\n"
                 "  endfunction\n"
                 "endinterface\n"
                 "module m;\n"
                 "  C c = new();\n"
                 "  ifc i();\n"
                 "  task automatic t(int a, output int o, input int b = 3);\n"
                 "    o = a * 10 + b;\n"
                 "  endtask\n"
                 "  initial begin\n"
                 "    int o;\n"
                 "    t(.o(o), .a(1));\n"
                 "    #1 $display(\"%0d %0d %0d %0d\", o, pk::pf(.b(7), "
                 ".a(2)), c.me(.a(3)), i.iff_(.b(8), .a(4)));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "13 27 35 48\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
