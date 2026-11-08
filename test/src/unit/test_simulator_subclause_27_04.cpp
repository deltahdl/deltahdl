#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(LoopGenerateHierarchicalNameSim, LocalparamIndexSelectsTheInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  localparam int K = 1;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "    int v;\n"
                       "    initial v = 36 + i;\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 $write(\"vidx %0d\", g[K].v);\n"
                       "    $display(\" %0d\", g[K - 1].v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "vidx 37 36\n");
}

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

TEST(LoopGenerateStaticFrameSim, AProceduresStaticLocalIsItsInstances) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : b\n"
                       "    initial begin\n"
                       "      static int s = i + 10;\n"
                       "      #(2 - i) s++;\n"
                       "      $display(\"s%0d %0d\", i, s);\n"
                       "    end\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "s1 12\ns0 11\n");
}

TEST(LoopGenerateStaticFrameSim, ANamedBlocksVariableIsItsInstances) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int r [2];\n"
                       "  for (genvar i = 0; i < 2; i++) begin : b\n"
                       "    initial repeat (2) begin : nb\n"
                       "      int c;\n"
                       "      c = c + i + 1;\n"
                       "      r[i] = c;\n"
                       "    end\n"
                       "  end\n"
                       "  initial #1 $display(\"%0d %0d\", r[0], r[1]);\n"
                       "endmodule\n",
                       f),
            "2 4\n");
}

TEST(LoopGenerateStaticFrameSim, ABlocksFunctionKeepsAStaticPerInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int n;\n"
                       "  function void bump(); static int c = 0; c++; "
                       "n = c; endfunction\n"
                       "  for (genvar i = 0; i < 2; i++) begin : b\n"
                       "    function int f(); static int s = 10 + i; s++; "
                       "return s; endfunction\n"
                       "    initial begin\n"
                       "      #(2 - i) $display(\"f%0d %0d\", i, f());\n"
                       "      bump();\n"
                       "    end\n"
                       "  end\n"
                       "  initial #3 $display(\"n %0d\", n);\n"
                       "endmodule\n",
                       f),
            "f1 12\nf0 11\nn 2\n");
}

TEST(LoopGenerateStaticFrameSim, AHierarchicalCallSharesTheInstancesFrame) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : b\n"
                       "    function int f(); static int s = 10 * (i + 1); "
                       "s++; return s; endfunction\n"
                       "    initial #(1 + i) $display(\"in%0d %0d\", i, f());\n"
                       "  end\n"
                       "  initial begin\n"
                       "    $display(\"h1 %0d\", b[1].f());\n"
                       "    $display(\"h0 %0d\", b[0].f());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "h1 21\nh0 11\nin0 12\nin1 22\n");
}

TEST(LoopGenerateStaticFrameSim, ANestedBlocksCallSharesTheDeclaringFrame) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : b\n"
                       "    function int f(); static int s = i * 10; s++; "
                       "return s; endfunction\n"
                       "    for (genvar j = 0; j < 2; j++) begin : c\n"
                       "      initial #(1 + 2 * i + j)\n"
                       "        $display(\"c%0d%0d %0d\", i, j, f());\n"
                       "    end\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "c00 1\nc01 2\nc10 11\nc11 12\n");
}

}  // namespace
