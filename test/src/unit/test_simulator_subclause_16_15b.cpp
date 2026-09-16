#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A design around the modules given, as test/src/e2e/disable_iff_resolution.sv
// is: the top t drives a 1, b 0, clk rising at 5, 15, 25 and 35, rst 1
// across the tick of 15 and rst1 across the tick of 35, and instantiates
// `instances`; the run ends at 40. Every attempt of a |=> b fails at the
// tick after its own unless its disable condition holds at either, so the
// times an assertion fails at say which condition it took: 15 and 25 for
// rst1, 35 for rst, and all three for none.
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

// §16.15 rules (a) and (b): the clause's a1 names rst1 in its own clause
// and a2 has it from p1, so the default rst is ignored for both and they
// fail at 15 and 25; a3 has no clause and infers rst, failing at 35 alone;
// a4 names 1'b0, the one way to cancel the default, and fails at every
// tick.
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

// §16.15 rule (c): with no default disable iff, the clause's a5 and a6 take
// the rst their own clause and p2 name, failing at 35, and a7 has no
// disable condition, failing at every tick.
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

// §16.15: the default extends to a nested module declaration, whose own
// default, where it declares one, overrides it, and its effect is
// independent of its position in the scope: m1 declares rst1 after its
// assertion, m2 declares none and inherits rst1, and m3 declares rst, so
// a_m1 and a_m2 fail at 15 and 25 and a_m3 at 35.
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

// §16.15: the scope of a default disable iff does not extend into an
// instance of a module declared elsewhere, so the assertion of `leaf`,
// instantiated in m1 under its default rst1, has no disable condition and
// fails at every tick; and a generate block with a default of its own
// applies it within the block, so a_gen takes rst and fails at 35.
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
