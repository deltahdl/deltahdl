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
  // §27.5 end-to-end over the §27.4 loop-generate dependency: a conditional
  // generate nested in a loop generate is selected per iteration using the
  // loop genvar as its constant. Only the i==2 iteration takes the (else-less)
  // then-branch, so exactly one continuous assignment to the module-level
  // result survives; the others select nothing. The input is built from real
  // loop-generate syntax and driven through the full pipeline, and the selected
  // block's assignment is observed by its simulated result.
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
  // §27.5 requires a conditional generate construct to select "at most one
  // generate block from a set of alternative generate blocks based on constant
  // expressions evaluated during elaboration", and to instantiate the selected
  // block into the model. Here no condition in the chain holds, so the final
  // else is the selected alternative and its 64 is the only value driven onto
  // the module-level variable the simulated run reads back. Elaborating the
  // else arm's body without evaluating the nested condition instantiates the
  // first else-if branch instead and yields 41, and never reaches the two
  // alternatives past it, so each of the four constants is distinct and
  // non-zero to name which alternative a wrong run selected.
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

// §27.5 with §23.6: a named conditional generate block is a scope, and what it
// declares is read from the module through the block's name. A 4-state value
// carrying an x bit keeps it through a part-select of the path.
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

// §27.5 with §23.6: a write from the module through the block's name lands in
// the variable the block's own process reads by its simple name.
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

// §27.5: the one block an if-else-if chain or a case generate selects is
// instantiated under the name its alternatives share, and a localparam it
// declares is read through that name. Each unselected alternative declares a
// different value, so reading one of them gives a different answer.
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

// §23.6: a path is usable from any scope, the method of a class the module
// declares among them.
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

// §23.6: the path may start at a submodule instance and pass through a block
// of that instance's module.
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

// §25.9 with §27.5: a virtual interface reaches what its interface instance
// declares, a named generate block's variable among it.
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

// §27.5 with §23.3: an instance written in the generate block a conditional
// generate construct selects is an ordinary instance of its module, so the
// module's own variable is declared and its procedures run: n counts the five
// rising edges of clk before 52.
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

// A concurrent assertion of a module instantiated in the selected block is
// evaluated as one outside it is: a is sampled 1, 0, 0, 1 and 1 at the five
// rising edges of clk, counted by the instance itself.
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

// The same counts read from the module through the block and the instance,
// `g.c.pass`, for a checker instantiated in the selected block.
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

}  // namespace
