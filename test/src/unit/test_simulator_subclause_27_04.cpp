#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §27.4: "Within the generate block of a loop generate construct, there is an
// implicit localparam declaration. This is an integer parameter that has the
// same name and type as the loop index, and its value within each instance of
// the generate block is the value of the loop index at the time the instance
// was elaborated." The genvar itself "does not exist at simulation time", so a
// reference to the name inside the block is a reference to that localparam.
//
// Every instance runs one shared body, so the value has to be private to the
// instance. Delaying each instance by a different amount interleaves the four
// bodies and makes the assignments run in the reverse of elaboration order: a
// value shared between the instances would leave every element holding the
// index of whichever instance ran last, rather than its own.
TEST(LoopGenerateIndexSim, IndexHoldsItsOwnInstanceValueAcrossADelay) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
                 "      initial begin\n"
                 "        #(4 - i);\n"
                 "        out[i] = i + 8'd10;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {10u, 11u, 12u, 13u});
}

// §27.4: each loop generate construct contributes its own implicit localparam,
// and a generate block nested in two of them is one instance of each. Both loop
// indices are therefore in scope in the innermost body, holding the values that
// selected this instance.
TEST(LoopGenerateIndexSim, NestedBlockSeesBothEnclosingIndices) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
                 "      for (genvar j = 0; j < 2; j = j + 1) begin : h\n"
                 "        initial out[i * 2 + j] = i * 8'd10 + j;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {0u, 1u, 10u, 11u});
}

// §27.4: the implicit localparam "can be used anywhere within the generate
// block that a normal parameter with an integer value can be used", which
// includes a continuous assignment. Each instance's assignment drives the
// element its own index selects, from a right-hand side its own index scales.
TEST(LoopGenerateIndexSim, ContinuousAssignmentSeesItsInstanceIndex) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
                 "      assign out[i] = i * 8'd3;\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {0u, 3u, 6u, 9u});
}

// §27.4: the loop index is an integer, so the parameter named after it is
// signed. A descending loop that runs the index negative therefore compares as
// negative, rather than wrapping to a large unsigned value.
TEST(LoopGenerateIndexSim, NegativeIndexIsSigned) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:2];\n"
                 "  generate\n"
                 "    for (genvar i = -1; i < 2; i = i + 1) begin : g\n"
                 "      initial out[i + 1] = (i < 0) ? 8'd7 : 8'd9;\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {7u, 9u, 9u});
}

// §27.4: a generate block "comprises a separate scope and a new level of
// hierarchy when it is instantiated", so a declaration inside the block belongs
// to the instance and is named by its simple name from within it. Each instance
// stores a different value in its own `x` and reads it back, so an instance
// finding nothing (or finding a neighbour's) shows up as the wrong element.
TEST(LoopGenerateIndexSim, BlockLocalDeclarationIsReadBackWithinItsInstance) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
                 "      logic [7:0] x;\n"
                 "      initial begin\n"
                 "        x = i + 8'd20;\n"
                 "        out[i] = x;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {20u, 21u, 22u, 23u});
}

// §27.4: the block's scope is the inner one, so a declaration in it hides a
// like-named declaration of the enclosing module for references written inside
// the block. The module-level `v` keeps the value its own process gave it,
// which distinguishes hiding from the instances writing through to it.
TEST(LoopGenerateIndexSim, BlockLocalDeclarationHidesTheModuleLevelName) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:1];\n"
                 "  logic [7:0] v;\n"
                 "  initial v = 8'd99;\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
                 "      logic [7:0] v;\n"
                 "      initial begin\n"
                 "        v = i + 8'd5;\n"
                 "        out[i] = v;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {5u, 6u});
  auto* outer = f.ctx.FindVariable("v");
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->value.ToUint64(), 99u);
}

// §27.4: a named generate block "is a declaration of an array of generate
// block instances", and "the index values in this array are the values assumed
// by the genvar during elaboration". Two sibling blocks written over one genvar
// are therefore two distinct arrays, and since each instance "comprises a
// separate scope and a new level of hierarchy when it is instantiated", `a`'s
// `x` at index 4 and `b`'s `x` at index 4 are different objects.
//
// Every instance writes its block's constant before any instance reads one
// back, so a run that gave the two blocks one object leaves both reads holding
// whichever write ran last, rather than each block's own constant. The loop
// runs 4 to 5 while the array it reports through is read at 0 to 3, so no index
// equals the offset of the element it selects.
TEST(LoopGenerateIndexSim, SiblingBlocksOverOneGenvarKeepSeparateVariables) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  genvar i;\n"
                 "  generate\n"
                 "    for (i = 4; i < 6; i = i + 1) begin : a\n"
                 "      logic [7:0] x;\n"
                 "      initial begin\n"
                 "        x = 8'd10;\n"
                 "        #1 out[i - 4] = x;\n"
                 "      end\n"
                 "    end\n"
                 "    for (i = 4; i < 6; i = i + 1) begin : b\n"
                 "      logic [7:0] x;\n"
                 "      initial begin\n"
                 "        x = 8'd20;\n"
                 "        #1 out[i - 2] = x;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {10u, 10u, 20u, 20u});
}

// §27.4 with §23.6: each instance of a loop generate block is a scope named by
// the block and the genvar value, `g[1]`, and what it declares is reached from
// outside through that name. A write from the module lands in the instance's
// own variable, which the instance then reads by its simple name.
TEST(LoopGenerateHierarchicalNameSim, WriteThroughTheInstanceNameReachesIt) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:1];\n"
                 "  for (genvar i = 0; i < 2; i++) begin : g\n"
                 "    logic [7:0] v;\n"
                 "    initial #1 out[i] = v;\n"
                 "  end\n"
                 "  initial begin g[0].v = 8'd80; g[1].v = 8'd81; end\n"
                 "endmodule\n",
                 "out", {80u, 81u});
}

// §27.4: what an instance of a loop block nested in another declares is read
// through both instance names, as §27.4's Example 5 names them: a localparam
// of the inner block and the implicit localparam of each loop index.
TEST(LoopGenerateHierarchicalNameSim, NestedInstanceDeclarationsAreRead) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  for (genvar i = 1; i < 3; i++) begin : B1\n"
                       "    for (genvar j = 0; j < 2; j++) begin : B2\n"
                       "      localparam int K = 7;\n"
                       "    end\n"
                       "  end\n"
                       "  initial $display(\"n %0d %0d %0d\", B1[1].B2[0].K, "
                       "B1[2].B2[1].j, B1[2].i);\n"
                       "endmodule\n",
                       f),
            "n 7 1 2\n");
}

// §27.4: the implicit localparam named as the loop index is a declaration of
// each instance, holding the index the instance was elaborated with, so it is
// read through the instance name like any other. The indices step by two so no
// instance's value is its position in the loop.
TEST(LoopGenerateHierarchicalNameSim, ImplicitIndexLocalparamIsRead) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  for (genvar i = 4; i < 8; i += 2) begin : g\n"
                       "  end\n"
                       "  initial $display(\"gv %0d %0d\", g[4].i, g[6].i);\n"
                       "endmodule\n",
                       f),
            "gv 4 6\n");
}

// §27.4 Example 4 declares a net in each instance of a loop block and names
// it `bitnum[k].t1`; the value its continuous assignment drives is read there.
TEST(LoopGenerateHierarchicalNameSim, InstanceNetIsRead) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int a = 12;\n"
                       "  for (genvar k = 0; k < 2; k++) begin : bitnum\n"
                       "    wire [31:0] t1;\n"
                       "    assign t1 = a + k;\n"
                       "  end\n"
                       "  initial #1 $display(\"t %0d %0d\", bitnum[0].t1, "
                       "bitnum[1].t1);\n"
                       "endmodule\n",
                       f),
            "t 12 13\n");
}

// §23.6: a path is usable from any scope, another generate block among them,
// and written inside a loop block its instance select may be the block's own
// loop index, which §27.4 makes a constant of the instance.
TEST(LoopGenerateHierarchicalNameSim, AnotherBlockSelectsByItsIndex) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:1];\n"
                 "  for (genvar i = 0; i < 2; i++) begin : a\n"
                 "    logic [7:0] v;\n"
                 "    initial v = 8'd12 + i;\n"
                 "  end\n"
                 "  for (genvar i = 0; i < 2; i++) begin : b\n"
                 "    initial #1 out[i] = a[1 - i].v;\n"
                 "  end\n"
                 "endmodule\n",
                 "out", {13u, 12u});
}

// §23.6: an instance select that is no constant, a variable of the module,
// selects the instance its value names when the read runs.
TEST(LoopGenerateHierarchicalNameSim, RunTimeIndexSelectsTheInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "    int v;\n"
                       "    initial v = 36 + i;\n"
                       "  end\n"
                       "  int k;\n"
                       "  initial begin\n"
                       "    #1 k = 1;\n"
                       "    $write(\"vidx %0d\", g[k].v);\n"
                       "    k = 0;\n"
                       "    $display(\" %0d\", g[k].v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "vidx 37 36\n");
}

// §27.4 with §23.6: a loop block declared in an interface is a scope of the
// interface instance, reached through the instance name and then the block's.
TEST(LoopGenerateHierarchicalNameSim, InterfaceInstanceBlockIsReached) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  for (genvar k = 0; k < 2; k++) begin : g\n"
                       "    int v;\n"
                       "    initial v = 100 + k;\n"
                       "  end\n"
                       "endinterface\n"
                       "module t;\n"
                       "  ifc u();\n"
                       "  initial #1 $display(\"if %0d %0d\", u.g[0].v, "
                       "u.g[1].v);\n"
                       "endmodule\n",
                       f),
            "if 100 101\n");
}

// §27.4 with §6.8: a declaration's initializer in a loop block is evaluated in
// the instance, where the loop index is that instance's implicit localparam,
// so each instance's e starts at its own value, 20 and 21. Read with the
// first instance's index everywhere, both instances started at 20.
TEST(LoopGenerateIndexSim, DeclarationInitializerReadsItsInstanceIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "    logic [7:0] e = 8'(i + 20);\n"
                       "  end\n"
                       "  initial #1 $display(\"e %0d %0d\", g[0].e, g[1].e);\n"
                       "endmodule\n",
                       f),
            "e 20 21\n");
}

// §27.4 with §23.3: an instance written in a loop generate block is an
// ordinary instance of its module in every block instance, so the module's
// own variable is declared and its procedures run: n counts the five rising
// edges of clk before 52.
TEST(LoopGenerateInstanceSim, ModuleInstanceInTheBlockRunsItsBody) {
  SimFixture f;
  std::string out = RunCapture(
      "module m2(input logic clk);\n"
      "  int n = 0;\n"
      "  always @(posedge clk) n <= n + 1;\n"
      "  initial #52 $display(\"n=%0d\", n);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  initial repeat (10) #5 clk = ~clk;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 1; i++) begin : g\n"
      "      m2 c(clk);\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "n=5\n");
}

// Each block instance's module instance evaluates its own concurrent
// assertion over a, sampled 1, 0, 0, 1 and 1 at the five rising edges of clk,
// and its counts are read through `g[i].c`. Every instance takes the one
// signal: a connection the genvar indexes is #4126's.
TEST(LoopGenerateInstanceSim, EachModuleInstanceEvaluatesItsAssertion) {
  SimFixture f;
  std::string out = RunCapture(
      "module m2(input logic a, input logic clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  logic a = 1;\n"
      "  initial repeat (10) #5 clk = ~clk;\n"
      "  initial begin #12 a = 0; #20 a = 1; end\n"
      "  for (genvar i = 0; i < 3; i++) begin : g\n"
      "    m2 c(a, clk);\n"
      "  end\n"
      "  initial #52 $display(\"%0d %0d %0d %0d %0d %0d\", g[0].c.pass,\n"
      "                       g[0].c.fail, g[1].c.pass, g[1].c.fail,\n"
      "                       g[2].c.pass, g[2].c.fail);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 2 3 2 3 2\n");
}

// The same for a checker instantiated in each block instance.
TEST(LoopGenerateInstanceSim, EachCheckerInstanceEvaluatesItsAssertion) {
  SimFixture f;
  std::string out = RunCapture(
      "checker chk(int id, logic a, logic clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  logic a = 1;\n"
      "  initial repeat (10) #5 clk = ~clk;\n"
      "  initial begin #12 a = 0; #20 a = 1; end\n"
      "  for (genvar i = 0; i < 3; i++) begin : g\n"
      "    chk c(i, a, clk);\n"
      "  end\n"
      "  initial #52 $display(\"%0d %0d %0d %0d %0d %0d\", g[0].c.pass,\n"
      "                       g[0].c.fail, g[1].c.pass, g[1].c.fail,\n"
      "                       g[2].c.pass, g[2].c.fail);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 2 3 2 3 2\n");
}

// §27.4's implicit localparam stands wherever a parameter may, so a localparam
// a loop block declares from it is a constant with a distinct value in each
// instance, read through the instance's name. The test fails on an elaborator
// that folds the declaration without the genvar's value, which leaves it
// unresolved and reads 0 in every instance.
TEST(LoopGenerateIndexSim, LocalparamFromTheIndexHoldsEachInstanceValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  genvar i;\n"
                       "  for (i = 0; i < 3; i = i + 1) begin : g\n"
                       "    localparam int K = i * 10;\n"
                       "  end\n"
                       "  initial $display(\"lp %0d %0d %0d\", g[0].K, g[1].K, "
                       "g[2].K);\n"
                       "endmodule\n",
                       f),
            "lp 0 10 20\n");
}

// The implicit localparam sizes a declared dimension as a parameter does, so
// each instance's variable is as wide as its own index gives. The test fails
// on an elaborator that sizes the dimension without the genvar's value, which
// falls back to one bit in every instance.
TEST(LoopGenerateIndexSim, IndexSizesEachInstanceDimension) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  genvar i;\n"
                       "  for (i = 1; i < 4; i = i + 1) begin : g\n"
                       "    logic [i-1:0] w;\n"
                       "    initial #(i) $write(\"%s%0d\", i == 1 ? \"dim \" : "
                       "\" \", $bits(w));\n"
                       "  end\n"
                       "  initial #4 $display(\"\");\n"
                       "endmodule\n",
                       f),
            "dim 1 2 3\n");
}

// The same through a localparam of the index, which is folded per instance
// before it sizes the dimension.
TEST(LoopGenerateIndexSim, LocalparamOfTheIndexSizesEachInstanceDimension) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  genvar i;\n"
                       "  for (i = 1; i < 4; i = i + 1) begin : g\n"
                       "    localparam int K = i * 2;\n"
                       "    logic [K-1:0] w;\n"
                       "    initial #(i) $write(\"%s%0d\", i == 1 ? \"lw \" : "
                       "\" \", $bits(w));\n"
                       "  end\n"
                       "  initial #4 $display(\"\");\n"
                       "endmodule\n",
                       f),
            "lw 2 4 6\n");
}

// §27.4 Example 5 overrides an instance's parameter from the implicit
// localparam, and §23.10 takes any constant expression of the instantiating
// scope, so each instance receives its own index. The test fails on an
// elaborator that resolves the override without the genvar's value, which
// leaves P at its default 0 in both instances.
TEST(LoopGenerateInstanceSim, NamedOverrideFromTheIndexReachesEachInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf #(parameter int P = 0);\n"
                       "  initial #(P - 99) $display(\"ip %0d\", P);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  genvar i;\n"
                       "  for (i = 100; i < 102; i = i + 1) begin : g\n"
                       "    leaf #(.P(i)) u();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ip 100\nip 101\n");
}

// The same through a positional override computed from the index.
TEST(LoopGenerateInstanceSim,
     PositionalOverrideFromTheIndexReachesEachInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf #(parameter int P = 0);\n"
                       "  initial #(P - 6) $display(\"ip %0d\", P);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  genvar i;\n"
                       "  for (i = 0; i < 2; i = i + 1) begin : g\n"
                       "    leaf #(i * 2 + 7) u();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ip 7\nip 9\n");
}

// §27.4 Example 3 indexes arrays by the implicit localparam in each instance's
// port connections, so instance g[k] reads src[2 - k] and drives dst[k]. The
// test fails on a simulator that evaluates the connections with no value for
// the genvar, which connects every instance to the wrong elements.
TEST(LoopGenerateInstanceSim, PortConnectionsReadTheInstanceIndex) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module add1(input logic [7:0] a, output logic [7:0] y);\n"
                 "  assign y = a + 1;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  logic [7:0] src [0:2];\n"
                 "  wire [7:0] dst [0:2];\n"
                 "  genvar i;\n"
                 "  for (i = 0; i < 3; i = i + 1) begin : g\n"
                 "    add1 u(.a(src[2 - i]), .y(dst[i]));\n"
                 "  end\n"
                 "  initial begin\n"
                 "    src[0] = 8; src[1] = 6; src[2] = 4;\n"
                 "    #1 $display(\"p %0d %0d %0d\", dst[0], dst[1], "
                 "dst[2]);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "p 5 7 9\n");
}

}  // namespace
