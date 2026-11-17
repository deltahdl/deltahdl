#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(CovergroupInstanceSim, SampleArgumentsBindToSampleFormals) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  covergroup cg with function sample(int x);\n"
                       "    coverpoint x { bins lo = {1}; bins hi = {3}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin c.sample(3); $display(\"cov=%0.2f\", "
                       "c.get_inst_coverage()); end\n"
                       "endmodule\n",
                       f),
            "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(OverriddenSampleMethodSim, AutomaticFunctionPassesItsLocalAndArgument) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  covergroup cg with function sample(bit [1:0] a, int x);\n"
                 "    coverpoint a { bins b[] = {[0:3]}; }\n"
                 "    coverpoint x { bins lo = {1}; bins hi = {5}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  function automatic void F(int j);\n"
                 "    bit [1:0] d;\n"
                 "    d = 2;\n"
                 "    c.sample(d, j);\n"
                 "  endfunction\n"
                 "  initial begin\n"
                 "    F(5);\n"
                 "    $display(\"%0.2f\", c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "37.50\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(OverriddenSampleMethodSim, ClassMethodSamplesItsEmbeddedCovergroup) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class K;\n"
                 "  covergroup cg with function sample(bit [1:0] a, int x);\n"
                 "    coverpoint a { bins b[] = {[0:3]}; }\n"
                 "    coverpoint x { bins lo = {1}; bins hi = {5}; }\n"
                 "  endgroup\n"
                 "  function new; cg = new; endfunction\n"
                 "  function automatic void F(int j);\n"
                 "    bit [1:0] d;\n"
                 "    d = 2;\n"
                 "    cg.sample(d, j);\n"
                 "  endfunction\n"
                 "endclass\n"
                 "module top;\n"
                 "  initial begin\n"
                 "    automatic K k = new;\n"
                 "    k.F(5);\n"
                 "    $display(\"%0.2f\", k.cg.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "37.50\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(OverriddenSampleMethodSim, SequenceMatchItemPassesALocalVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit clk, a, b;\n"
                       "  int d;\n"
                       "  covergroup cg with function sample(int x);\n"
                       "    coverpoint x { bins two = {2}; bins one = {1}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  property p;\n"
                       "    int v;\n"
                       "    @(posedge clk) (a, v = d) ##1 (b, c.sample(v));\n"
                       "  endproperty\n"
                       "  cover property (p);\n"
                       "  initial begin\n"
                       "    a = 1; b = 1; d = 2;\n"
                       "    #1 clk = 1; #1 clk = 0; d = 0;\n"
                       "    #1 clk = 1; #1 clk = 0;\n"
                       "    $display(\"%0.2f\", c.get_inst_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(OverriddenSampleMethodSim, AFormalHidesTheEnclosingVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int x = 7;\n"
                       "  covergroup cg with function sample(int x);\n"
                       "    coverpoint x { bins five = {5}; bins one = {1}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    c.sample(5);\n"
                       "    $display(\"%0.2f\", c.get_inst_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(OverriddenSampleMethodSim, ANonFormalNameReadsTheEnclosingScope) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  int w = 2;\n"
                 "  int k;\n"
                 "  covergroup cg with function sample(int x);\n"
                 "    cx: coverpoint x { bins b = {1}; option.weight = k; }\n"
                 "    cw: coverpoint w { bins two = {2}; bins three = {3}; }\n"
                 "  endgroup\n"
                 "  cg c;\n"
                 "  initial begin\n"
                 "    k = 3;\n"
                 "    c = new;\n"
                 "    c.sample(1);\n"
                 "    $display(\"%0.2f\", c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "87.50\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(OverriddenSampleMethodSim, DISABLED_AFormalCrossedInAModuleCovergroup) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  covergroup cg with function sample(bit a, bit v);\n"
                       "    coverpoint v;\n"
                       "    X: cross v, a;\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    c.sample(1, 0);\n"
                       "    $display(\"%0.2f\", c.X.get_inst_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "25.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(OverriddenSampleMethodSim, DISABLED_AFormalCrossedInAClassCovergroup) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class K;\n"
                       "  covergroup cg with function sample(bit a, bit v);\n"
                       "    coverpoint v;\n"
                       "    X: cross v, a;\n"
                       "  endgroup\n"
                       "  function new; cg = new; endfunction\n"
                       "endclass\n"
                       "module top;\n"
                       "  initial begin\n"
                       "    automatic K k = new;\n"
                       "    k.cg.sample(1, 0);\n"
                       "    $display(\"%0.2f\", k.cg.X.get_inst_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "25.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
