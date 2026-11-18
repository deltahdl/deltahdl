#include <gtest/gtest.h>

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunInLoopBlock(const std::string& items,
                           const std::string& report) {
  SimFixture f;
  return RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int got [0:3];\n"
      "  int hits [0:3];\n"
      "  function automatic void put(int k, int v);\n"
      "    got[k] = v;\n"
      "  endfunction\n"
      "  initial repeat (4) #5 clk = ~clk;\n"
      "  for (genvar i = 2; i <= 3; i++) begin : g\n"
      "    localparam int K = i;\n" +
          items +
          "  end\n"
          "  initial #30 $display(" +
          report +
          ");\n"
          "endmodule\n",
      f);
}

constexpr const char* kGot = "\"%0d %0d\", got[2], got[3]";

TEST(LoopGenerateAssertionActionSim, DISABLED_ACoverPropertyPassReadsTheIndex) {
  EXPECT_EQ(RunInLoopBlock(
                "    cover property (@(posedge clk) 1) got[K] = i;\n", kGot),
            "2 3\n");
}

TEST(LoopGenerateAssertionActionSim,
     DISABLED_AnAssertPropertyPassReadsTheIndex) {
  EXPECT_EQ(RunInLoopBlock(
                "    assert property (@(posedge clk) 1) got[K] = i;\n", kGot),
            "2 3\n");
}

TEST(LoopGenerateAssertionActionSim, DISABLED_AnElseActionReadsTheIndex) {
  for (const std::string& kind : {"assert", "assume"}) {
    EXPECT_EQ(RunInLoopBlock("    " + kind +
                                 " property (@(posedge clk) 0) else got[K] = "
                                 "i;\n",
                             kGot),
              "2 3\n")
        << kind;
  }
}

TEST(LoopGenerateAssertionActionSim,
     DISABLED_ACoverSequenceActionReadsTheIndex) {
  EXPECT_EQ(RunInLoopBlock(
                "    cover sequence (@(posedge clk) 1) got[K] = i;\n", kGot),
            "2 3\n");
}

TEST(LoopGenerateAssertionActionSim,
     DISABLED_ANestedLoopsActionReadsBothIndices) {
  EXPECT_EQ(RunInLoopBlock("    for (genvar j = 5; j <= 5; j++) begin : h\n"
                           "      cover property (@(posedge clk) 1)\n"
                           "        got[K] = i * 10 + j;\n"
                           "    end\n",
                           kGot),
            "25 35\n");
}

TEST(LoopGenerateAssertionActionSim,
     DISABLED_AnExpressionAndASelectReadTheIndex) {
  EXPECT_EQ(RunInLoopBlock("    cover property (@(posedge clk) 1) begin\n"
                           "      got[K] = i * 10;\n"
                           "      hits[i] = 1;\n"
                           "    end\n",
                           "\"%0d %0d %0d %0d %0d %0d\", got[2], got[3], "
                           "hits[0], hits[1], hits[2], hits[3]"),
            "20 30 0 0 1 1\n");
}

std::vector<std::string> SortedLines(const std::string& text) {
  std::vector<std::string> lines;
  std::istringstream in(text);
  for (std::string line; std::getline(in, line);) lines.push_back(line);
  std::sort(lines.begin(), lines.end());
  return lines;
}

TEST(LoopGenerateAssertionActionSim, DISABLED_EachDesignElementReadsTheIndex) {
  const std::string kBody =
      "  for (genvar i = 2; i <= 3; i++) begin : g\n"
      "    cover property (@(posedge clk) 1) $display(\"%m %0d\", i);\n"
      "  end\n";
  SimFixture f;
  std::string out = RunCapture("interface ifc(input logic clk);\n" + kBody +
                                   "endinterface\n"
                                   "checker chk(logic clk);\n" +
                                   kBody +
                                   "endchecker\n"
                                   "program prg(input logic clk);\n" +
                                   kBody +
                                   "endprogram\n"
                                   "module t;\n"
                                   "  logic clk = 0;\n"
                                   "  initial repeat (2) #5 clk = ~clk;\n"
                                   "  ifc u(clk);\n"
                                   "  chk c(clk);\n"
                                   "  prg p(clk);\n"
                                   "endmodule\n",
                               f);
  EXPECT_EQ(SortedLines(out), (std::vector<std::string>{
                                  "t.c.g[2] 2", "t.c.g[3] 3", "t.p.g[2] 2",
                                  "t.p.g[3] 3", "t.u.g[2] 2", "t.u.g[3] 3"}));
}

TEST(LoopGenerateAssertionActionSim, AnImmediateAssertionsActionsReadTheIndex) {
  EXPECT_EQ(RunInLoopBlock("    initial begin\n"
                           "      assert (1) got[K] = i;\n"
                           "      assert (0) else hits[K] = i;\n"
                           "    end\n",
                           "\"%0d %0d %0d %0d\", got[2], got[3], hits[2], "
                           "hits[3]"),
            "2 3 2 3\n");
}

TEST(LoopGenerateAssertionActionSim, ADeferredAssertionsActionReadsTheIndex) {
  EXPECT_EQ(RunInLoopBlock(
                "    always @(posedge clk) assert #0 (1) put(K, i);\n", kGot),
            "2 3\n");
}

TEST(LoopGenerateAssertionActionSim,
     AProceduralConcurrentAssertionsActionReadsTheIndex) {
  EXPECT_EQ(
      RunInLoopBlock(
          "    always @(posedge clk) cover property (1) got[K] = i;\n", kGot),
      "2 3\n");
}

TEST(LoopGenerateAssertionActionSim, ALocalparamOfTheIndexIsReadInTheAction) {
  EXPECT_EQ(
      RunInLoopBlock("    cover property (@(posedge clk) 1) got[K] = K * 10;\n",
                     kGot),
      "20 30\n");
}

TEST(LoopGenerateHierarchicalNameSim, ANegativeIndexNamesItsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  for (genvar i = -1; i < 1; i++) begin : g\n"
                       "    int x = i + 7;\n"
                       "  end\n"
                       "  initial #1 $display(\"%0d %0d\", g[-1].x, g[0].x);\n"
                       "endmodule\n",
                       f),
            "6 7\n");
}

TEST(GenerateBlockPrimitiveSim, AGateInALoopBlockDrivesItsOwnBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [3:0] a = 4'b1100, b = 4'b1010;\n"
                       "  wire [3:0] o;\n"
                       "  for (genvar i = 0; i < 4; i++) begin : g\n"
                       "    and a1(o[i], a[i], b[i]);\n"
                       "  end\n"
                       "  initial #1 $display(\"%b\", o);\n"
                       "endmodule\n",
                       f),
            "1000\n");
}

TEST(GenerateBlockPrimitiveSim, AMosSwitchInALoopBlockPassesItsOwnBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [1:0] d = 2'b10;\n"
                       "  logic c = 1;\n"
                       "  wire [1:0] y;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "    nmos n1(y[i], d[i], c);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b\", y);\n"
                       "    c = 0;\n"
                       "    #1 $display(\"%b\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "10\nzz\n");
}

TEST(GenerateBlockPrimitiveSim, AMosSwitchInAConditionalBlockConducts) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic d = 1, c = 1;\n"
                       "  wire y;\n"
                       "  if (1) begin : g\n"
                       "    nmos n1(y, d, c);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b\", y);\n"
                       "    c = 0;\n"
                       "    #1 $display(\"%b\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\nz\n");
}

TEST(GenerateBlockPrimitiveSim,
     DISABLED_APassSwitchInALoopBlockJoinsItsOwnPair) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [1:0] da = 2'b01;\n"
                       "  logic [1:0] db = 2'bzz;\n"
                       "  logic c = 1;\n"
                       "  wire [1:0] a, b;\n"
                       "  assign a = da;\n"
                       "  assign b = db;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "    tranif1 t1(a[i], b[i], c);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b\", b);\n"
                       "    da = 2'bzz;\n"
                       "    db = 2'b10;\n"
                       "    #1 $display(\"%b\", a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "01\n10\n");
}

TEST(GenerateBlockPrimitiveSim, APassSwitchInAConditionalBlockJoinsBothWays) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic da = 1, db = 1'bz;\n"
                       "  wire a, b;\n"
                       "  assign a = da;\n"
                       "  assign b = db;\n"
                       "  if (1) begin : g\n"
                       "    tran t1(a, b);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b\", b);\n"
                       "    da = 1'bz;\n"
                       "    db = 0;\n"
                       "    #1 $display(\"%b\", a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n0\n");
}

TEST(GenerateBlockPrimitiveSim, AUdpInAConditionalBlockDrivesFromItsTable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive udp_inv(output y, input a);\n"
                       "  table\n"
                       "    0 : 1;\n"
                       "    1 : 0;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "module t;\n"
                       "  logic a = 0;\n"
                       "  wire y;\n"
                       "  if (1) begin : g\n"
                       "    udp_inv u(y, a);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b\", y);\n"
                       "    a = 1;\n"
                       "    #1 $display(\"%b\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n0\n");
}

TEST(BeginlessLoopBodySim, ADeclarationHidesTheModuleNameInEachInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int x = 100;\n"
                       "  for (genvar i = 0; i < 2; i++)\n"
                       "    int x = i;\n"
                       "  initial #1 $display(\"%0d\", x);\n"
                       "endmodule\n",
                       f),
            "100\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BeginlessLoopBodySim, ANestedConstructFormsAScopePerInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int out [0:3];\n"
                       "  for (genvar i = 0; i < 2; i++)\n"
                       "    for (genvar j = 0; j < 2; j++)\n"
                       "      initial out[i * 2 + j] = i * 10 + j;\n"
                       "  initial #1 $display(\"%0d %0d %0d %0d\", out[0], "
                       "out[1], out[2], out[3]);\n"
                       "endmodule\n",
                       f),
            "0 1 10 11\n");
}

TEST(BeginlessLoopBodySim, AProceduresStaticLocalIsEachInstances) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int out [0:1];\n"
                       "  for (genvar i = 0; i < 2; i++)\n"
                       "    initial begin : p\n"
                       "      static int n = 0;\n"
                       "      #(i + 1) n = n + 1;\n"
                       "      out[i] = n;\n"
                       "    end\n"
                       "  initial #5 $display(\"%0d %0d\", out[0], out[1]);\n"
                       "endmodule\n",
                       f),
            "1 1\n");
}

TEST(LoopIndexLocalparamSim, ItExistsInAProgramsLoopBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program t;\n"
                       "  int out [0:2];\n"
                       "  for (genvar i = 0; i < 3; i++) begin : g\n"
                       "    initial out[i] = i + 40;\n"
                       "  end\n"
                       "  initial #1 $display(\"%0d %0d %0d\", out[0], "
                       "out[1], out[2]);\n"
                       "endprogram\n",
                       f),
            "40 41 42\n");
}

TEST(LoopIndexLocalparamSim, DISABLED_ItIsAThirtyTwoBitInteger) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "    localparam int B = $bits(i);\n"
                       "    initial #(i + 1) $display(\"%0d %0d\", B, "
                       "$bits(i));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "32 32\n32 32\n");
}

TEST(UnnamedGenerateBlockSim, ANameIsReadByItsSimpleNameWithinTheBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  if (1) begin\n"
                       "    int a = 7;\n"
                       "    initial #1 $display(\"%0d\", a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7\n");
}

TEST(UnnamedGenerateBlockSim, DISABLED_ANameReachesANamedBlockNestedInIt) {
  for (const std::string& header :
       {"  if (1) begin\n", "  for (genvar i = 0; i < 1; i++) begin\n"}) {
    SimFixture f;
    EXPECT_EQ(RunCapture("module t;\n" + header +
                             "    if (1) begin : n\n"
                             "      int x = 5;\n"
                             "    end\n"
                             "    initial #1 $display(\"%0d\", n.x);\n"
                             "  end\n"
                             "endmodule\n",
                         f),
              "5\n")
        << header;
  }
}

}  // namespace
