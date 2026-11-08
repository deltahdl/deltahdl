#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Design(const std::string& modules, const std::string& instances) {
  return modules +
         "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 1, b = 0, rst = 0, rst1 = 0;\n"
         "  always #5 clk = ~clk;\n" +
         instances +
         "  initial begin\n"
         "    #12 rst = 1;\n"
         "    #6 rst = 0;\n"
         "    #14 rst1 = 1;\n"
         "    #6 rst1 = 0;\n"
         "    #2 $finish;\n"
         "  end\n"
         "endmodule\n";
}

const char* const kWithDefault =
    "module examples_with_default(input logic a, b, clk, rst, rst1);\n"
    "  default disable iff rst;\n"
    "  property p1;\n"
    "    disable iff (rst1) a |=> b;\n"
    "  endproperty\n"
    "  a1: assert property (@(posedge clk) disable iff (rst1) a |=> b)\n"
    "    else $display(\"a1 failed at %0d\", $time);\n"
    "  a2: assert property (@(posedge clk) p1)\n"
    "    else $display(\"a2 failed at %0d\", $time);\n"
    "  a3: assert property (@(posedge clk) a |=> b)\n"
    "    else $display(\"a3 failed at %0d\", $time);\n"
    "  a4: assert property (@(posedge clk) disable iff (1'b0) a |=> b)\n"
    "    else $display(\"a4 failed at %0d\", $time);\n"
    "endmodule\n";

TEST(DisableIffResolutionRun, AnOwnClauseWinsAndTheDefaultIsInferredOtherwise) {
  SimFixture f;
  std::string out =
      RunCapture(Design(kWithDefault,
                        "  examples_with_default u1(a, b, clk, rst, rst1);\n"),
                 f);
  EXPECT_EQ(out,
            "a1 failed at 15\na2 failed at 15\na4 failed at 15\n"
            "a1 failed at 25\na2 failed at 25\na4 failed at 25\n"
            "a3 failed at 35\na4 failed at 35\n$finish at time 40\n");
}

TEST(DisableIffResolutionRun, WithoutADefaultNoConditionIsInferred) {
  SimFixture f;
  std::string out = RunCapture(
      Design(
          "module examples_without_default(input logic a, b, clk, rst);\n"
          "  property p2;\n"
          "    disable iff (rst) a |=> b;\n"
          "  endproperty\n"
          "  a5: assert property (@(posedge clk) disable iff (rst) a |=> b)\n"
          "    else $display(\"a5 failed at %0d\", $time);\n"
          "  a6: assert property (@(posedge clk) p2)\n"
          "    else $display(\"a6 failed at %0d\", $time);\n"
          "  a7: assert property (@(posedge clk) a |=> b)\n"
          "    else $display(\"a7 failed at %0d\", $time);\n"
          "endmodule\n",
          "  examples_without_default u2(a, b, clk, rst);\n"),
      f);
  EXPECT_EQ(out,
            "a7 failed at 15\na7 failed at 25\n"
            "a5 failed at 35\na6 failed at 35\na7 failed at 35\n"
            "$finish at time 40\n");
}

TEST(DisableIffResolutionRun, ANestedDeclarationInheritsOrOverridesTheDefault) {
  SimFixture f;
  std::string out =
      RunCapture(Design("module m1(input logic a, b, clk, rst, rst1);\n"
                        "  a_m1: assert property (@(posedge clk) a |=> b)\n"
                        "    else $display(\"a_m1 failed at %0d\", $time);\n"
                        "  default disable iff rst1;\n"
                        "  module m2;\n"
                        "    a_m2: assert property (@(posedge clk) a |=> b)\n"
                        "      else $display(\"a_m2 failed at %0d\", $time);\n"
                        "  endmodule\n"
                        "  module m3;\n"
                        "    default disable iff rst;\n"
                        "    a_m3: assert property (@(posedge clk) a |=> b)\n"
                        "      else $display(\"a_m3 failed at %0d\", $time);\n"
                        "  endmodule\n"
                        "endmodule\n",
                        "  m1 u1(a, b, clk, rst, rst1);\n"),
                 f);
  EXPECT_EQ(out,
            "a_m1 failed at 15\na_m2 failed at 15\n"
            "a_m1 failed at 25\na_m2 failed at 25\n"
            "a_m3 failed at 35\n$finish at time 40\n");
}

TEST(DisableIffResolutionRun,
     TheDefaultStopsAtAnInstanceAndAGenerateBlockMayOverrideIt) {
  SimFixture f;
  std::string out =
      RunCapture(Design("module leaf(input logic a, b, clk);\n"
                        "  a_leaf: assert property (@(posedge clk) a |=> b)\n"
                        "    else $display(\"a_leaf failed at %0d\", $time);\n"
                        "endmodule\n"
                        "module m1(input logic a, b, clk, rst, rst1);\n"
                        "  default disable iff rst1;\n"
                        "  leaf u_leaf(a, b, clk);\n"
                        "  if (1) begin : gen\n"
                        "    default disable iff rst;\n"
                        "    a_gen: assert property (@(posedge clk) a |=> b)\n"
                        "      else $display(\"a_gen failed at %0d\", $time);\n"
                        "  end\n"
                        "endmodule\n",
                        "  m1 u1(a, b, clk, rst, rst1);\n"),
                 f);
  EXPECT_EQ(out,
            "a_leaf failed at 15\na_leaf failed at 25\n"
            "a_leaf failed at 35\na_gen failed at 35\n$finish at time 40\n");
}

}  // namespace
