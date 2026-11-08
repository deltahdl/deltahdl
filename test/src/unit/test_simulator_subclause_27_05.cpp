#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(GenerateSimulation, GenerateIfTrueBranch) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter N = 1) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (N > 0) begin\n"
      "      assign x = 42;\n"
      "    end else begin\n"
      "      assign x = 0;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(GenerateSimulation, GenerateIfFalseBranch) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter N = 0) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (N > 0) begin\n"
      "      assign x = 42;\n"
      "    end else begin\n"
      "      assign x = 99;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(GenerateSimulation, GenerateCaseMatch) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter MODE = 2) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    case (MODE)\n"
      "      1: begin assign x = 10; end\n"
      "      2: begin assign x = 20; end\n"
      "      3: begin assign x = 30; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(GenerateSimulation, GenerateCaseDefault) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter MODE = 99) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    case (MODE)\n"
      "      1: begin assign x = 10; end\n"
      "      2: begin assign x = 20; end\n"
      "      default: begin assign x = 77; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(GenerateSimulation, GenerateIfNoElseFalse) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter EN = 0) ();\n"
      "  logic [31:0] x;\n"
      "  assign x = 5;\n"
      "  generate\n"
      "    if (EN) begin\n"
      "      assign x = 99;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(GenerateSimulation, GenerateCaseNoMatchNoDefault) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter MODE = 42) ();\n"
      "  logic [31:0] x;\n"
      "  assign x = 3;\n"
      "  generate\n"
      "    case (MODE)\n"
      "      1: begin assign x = 10; end\n"
      "      2: begin assign x = 20; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(GenerateSimulation, GenerateIfElseIfChainSelectsMiddle) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter SEL = 1) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (SEL == 0) begin\n"
      "      assign x = 10;\n"
      "    end else if (SEL == 1) begin\n"
      "      assign x = 55;\n"
      "    end else begin\n"
      "      assign x = 99;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(GenerateSimulation, GenerateCaseMultiplePatternsPerItem) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter SEL = 2) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    case (SEL)\n"
      "      0, 1, 2: begin assign x = 11; end\n"
      "      default: begin assign x = 88; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(GenerateSimulation, GenvarGatedConditionalDrivesValue) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t ();\n"
      "  logic [31:0] r;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
      "      if (i == 2) begin\n"
      "        assign r = 77;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(GenerateSimulation, GenerateIfElseIfChainSelectsFinalElse) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter SEL = 7) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (SEL == 0) begin\n"
      "      assign x = 13;\n"
      "    end else if (SEL == 1) begin\n"
      "      assign x = 41;\n"
      "    end else if (SEL == 2) begin\n"
      "      assign x = 26;\n"
      "    end else begin\n"
      "      assign x = 64;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 64u);
}

TEST(ConditionalGenerateHierarchicalNameSim, BlockVariableIsReadWhole) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  if (1) begin : g\n"
                       "    logic [3:0] v;\n"
                       "    string s;\n"
                       "    initial begin v = 4'b001x; s = \"hello\"; end\n"
                       "  end\n"
                       "  initial #1 $display(\"lg %b %b %s\", g.v, "
                       "g.v[1:0], g.s);\n"
                       "endmodule\n",
                       f),
            "lg 001x 1x hello\n");
}

TEST(ConditionalGenerateHierarchicalNameSim, WriteFromTheModuleReachesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  if (1) begin : g\n"
                       "    int v;\n"
                       "    initial #1 $display(\"wr %0d\", v);\n"
                       "  end\n"
                       "  initial g.v = 78;\n"
                       "endmodule\n",
                       f),
            "wr 78\n");
}

TEST(ConditionalGenerateHierarchicalNameSim, SelectedBlockLocalparamIsRead) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  localparam int P = 2;\n"
                 "  if (P == 1) begin : u localparam int R = 1; end\n"
                 "  else if (P == 2) begin : u localparam int R = 3; end\n"
                 "  else begin : u localparam int R = 5; end\n"
                 "  case (P)\n"
                 "    1: begin : adder localparam int K = 7; end\n"
                 "    2, 3: begin : adder localparam int K = 8; end\n"
                 "    default: begin : adder localparam int K = 9; end\n"
                 "  endcase\n"
                 "  initial $display(\"sel %0d %0d\", u.R, adder.K);\n"
                 "endmodule\n",
                 f),
      "sel 3 8\n");
}

TEST(ConditionalGenerateHierarchicalNameSim, ClassMethodReadsThroughIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  if (1) begin : g\n"
                       "    int v;\n"
                       "    initial v = 33;\n"
                       "  end\n"
                       "  class C;\n"
                       "    function int get(); return g.v; endfunction\n"
                       "  endclass\n"
                       "  initial begin\n"
                       "    automatic C c = new;\n"
                       "    #1 $display(\"meth %0d\", c.get());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "meth 33\n");
}

TEST(ConditionalGenerateHierarchicalNameSim, SubmoduleBlockIsReached) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  if (1) begin : g\n"
                       "    int v;\n"
                       "    initial v = 29;\n"
                       "  end\n"
                       "endmodule\n"
                       "module t;\n"
                       "  sub u();\n"
                       "  initial #1 $display(\"hi %0d\", u.g.v);\n"
                       "endmodule\n",
                       f),
            "hi 29\n");
}

TEST(ConditionalGenerateHierarchicalNameSim, VirtualInterfaceReachesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  if (1) begin : g\n"
                       "    int v;\n"
                       "  end\n"
                       "endinterface\n"
                       "module t;\n"
                       "  ifc u();\n"
                       "  virtual ifc vi;\n"
                       "  initial begin\n"
                       "    vi = u;\n"
                       "    vi.g.v = 55;\n"
                       "    #1 $display(\"vif %0d %0d\", u.g.v, vi.g.v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "vif 55 55\n");
}

TEST(GenerateSimulation, ModuleInstanceInTheSelectedBlockRunsItsBody) {
  SimFixture f;
  std::string out = RunCapture(
      "module m2(input logic clk);\n"
      "  int n = 0;\n"
      "  always_ff @(posedge clk) n <= n + 1;\n"
      "  initial #52 $display(\"n=%0d\", n);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  initial repeat (10) #5 clk = ~clk;\n"
      "  if (1) begin : g\n"
      "    m2 c(clk);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "n=5\n");
}

TEST(GenerateSimulation,
     ModuleInstanceInTheSelectedBlockEvaluatesItsAssertion) {
  SimFixture f;
  std::string out = RunCapture(
      "module m2(input logic a, input logic clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
      "  initial #52 $display(\"pass=%0d fail=%0d\", pass, fail);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  initial repeat (10) #5 clk = ~clk;\n"
      "  if (1) begin : g\n"
      "    m2 c(a, clk);\n"
      "  end\n"
      "  initial begin #12 a = 0; #20 a = 1; end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "pass=3 fail=2\n");
}

TEST(GenerateSimulation, CheckerInstanceInTheSelectedBlockEvaluatesIt) {
  SimFixture f;
  std::string out = RunCapture(
      "checker chk(logic a, logic clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  parameter bit USE = 1;\n"
      "  logic clk = 0, a = 1;\n"
      "  initial repeat (10) #5 clk = ~clk;\n"
      "  if (USE) begin : g\n"
      "    chk c(a, clk);\n"
      "  end\n"
      "  initial begin #12 a = 0; #20 a = 1; end\n"
      "  initial #52 $display(\"pass=%0d fail=%0d\", g.c.pass, g.c.fail);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "pass=3 fail=2\n");
}

TEST(GenerateSimulation, BitsOfATypeParameterGatesAGenerateIf) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top #(parameter type T = logic [15:0]);\n"
                       "  if ($bits(T) > 8) begin : g\n"
                       "    initial $display(\"bits wide\");\n"
                       "  end else begin : g\n"
                       "    initial $display(\"bits narrow\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "bits wide\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(GenerateSimulation, BindTargetsAnInstanceInsideAGenerateBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf(input logic [7:0] a);\n"
                       "endmodule\n"
                       "module mon(input logic [7:0] a);\n"
                       "  initial #1 $display(\"bnd %0d\", a);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic [7:0] x = 35;\n"
                       "  if (1) begin : g\n"
                       "    leaf u(x);\n"
                       "  end\n"
                       "  bind top.g.u mon m(.a(a));\n"
                       "endmodule\n",
                       f),
            "bnd 35\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(GenerateSimulation, GenerateBlockOfABoundModuleRuns) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n"
                       "endmodule\n"
                       "module mon;\n"
                       "  if (1) begin : g\n"
                       "    initial #1 $display(\"bnd gen\");\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  leaf u();\n"
                       "  bind leaf mon m();\n"
                       "endmodule\n",
                       f),
            "bnd gen\n");
}

TEST(GenerateSimulation, EachBlockReadsTheLocalparamItDeclares) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  if (1) begin : a\n"
                       "    localparam int K = 3;\n"
                       "    initial #1 $write(\"two %0d\", K);\n"
                       "  end\n"
                       "  if (1) begin : b\n"
                       "    localparam int K = 4;\n"
                       "    initial #2 $display(\" %0d\", K);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "two 3 4\n");
}

TEST(GenerateSimulation, BlockLocalparamHidesTheModuleParameterInTheBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  parameter int K = 1;\n"
                       "  if (1) begin : g\n"
                       "    localparam int K = 9;\n"
                       "    initial $display(\"sh %0d %0d\", K, top.K);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "sh 9 1\n");
}

TEST(GenerateSimulation, EachIterationReadsItsSelectedBlocksLocalparam) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  genvar i;\n"
                       "  for (i = 0; i < 2; i = i + 1) begin : g\n"
                       "    case (i)\n"
                       "      0: begin : c\n"
                       "        localparam int K = 7;\n"
                       "        initial #1 $display(\"cs5 %0d\", K);\n"
                       "      end\n"
                       "      default: begin : c\n"
                       "        localparam int K = 8;\n"
                       "        initial #2 $display(\"cs5 %0d\", K);\n"
                       "      end\n"
                       "    endcase\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "cs5 7\ncs5 8\n");
}

TEST(GenerateSimulation, InterfaceInstanceInALoopBlockIsConnected) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  int d;\n"
                       "endinterface\n"
                       "module cons(ifc i);\n"
                       "  initial #1 $display(\"ifp %0d\", i.d);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  genvar k;\n"
                       "  for (k = 0; k < 2; k = k + 1) begin : g\n"
                       "    ifc i();\n"
                       "    cons c(i);\n"
                       "    initial i.d = 32 + k;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ifp 32\nifp 33\n");
}

TEST(GenerateSimulation, InterfaceModportInAConditionalBlockIsConnected) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  int d;\n"
                       "  modport m(input d);\n"
                       "endinterface\n"
                       "module cons(ifc.m p);\n"
                       "  initial #1 $display(\"mp %0d\", p.d);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  if (1) begin : g\n"
                       "    ifc i();\n"
                       "    cons c(i.m);\n"
                       "    initial i.d = 70;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "mp 70\n");
}

TEST(GenerateSimulation, ModuleInterfaceInstanceIsConnectedInsideABlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  int d;\n"
                       "endinterface\n"
                       "module cons(ifc p);\n"
                       "  initial #1 $display(\"oi %0d\", p.d);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  ifc i();\n"
                       "  initial i.d = 72;\n"
                       "  if (1) begin : g\n"
                       "    cons c(i);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "oi 72\n");
}

}  // namespace
