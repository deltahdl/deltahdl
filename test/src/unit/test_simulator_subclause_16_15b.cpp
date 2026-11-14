#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_disable_iff_runs.h"

using namespace delta;

namespace {

std::string Design(const std::string& modules, const std::string& instances) {
  return DisableIffDesign(modules, instances);
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

TEST(DisableIffResolutionRun, ADefaultsBinaryOperatorOperandIsEvaluatedWhole) {
  SimFixture f;
  std::string out =
      RunCapture(Design("module m(input logic a, b, clk, rst, rst1);\n"
                        "  default disable iff rst || rst1;\n"
                        "  a_or: assert property (@(posedge clk) a |=> b)\n"
                        "    else $display(\"a_or failed at %0d\", $time);\n"
                        "endmodule\n",
                        "  m u(a, b, clk, rst, rst1);\n"),
                 f);
  EXPECT_EQ(out, "$finish at time 40\n");
}

TEST(DisableIffResolutionRun,
     DISABLED_ADefaultsDistOperandDisablesWhereTheValueIsInItsSet) {
  SimFixture f;
  std::string out =
      RunCapture(Design("module d0(input logic a, b, clk, rst1);\n"
                        "  default disable iff rst1 dist {0 := 1};\n"
                        "  a_d0: assert property (@(posedge clk) a |=> b)\n"
                        "    else $display(\"a_d0 failed at %0d\", $time);\n"
                        "endmodule\n"
                        "module d1(input logic a, b, clk, rst);\n"
                        "  default disable iff rst dist {[1:2] :/ 1};\n"
                        "  a_d1: assert property (@(posedge clk) a |=> b)\n"
                        "    else $display(\"a_d1 failed at %0d\", $time);\n"
                        "endmodule\n",
                        "  d0 u0(a, b, clk, rst1);\n"
                        "  d1 u1(a, b, clk, rst);\n"),
                 f);
  EXPECT_EQ(out, "a_d1 failed at 35\n$finish at time 40\n");
}

std::string SortedResolutionLines(const std::string& default_decl) {
  SimFixture f;
  std::string out = RunCapture(
      Design("module kinds(input logic a, b, clk, rst, rst1);\n" +
                 default_decl +
                 "  property p1; disable iff (rst1) a |=> b; endproperty\n"
                 "  m_inf: assume property (@(posedge clk) a |=> b)\n"
                 "    else $display(\"m_inf %0d\", $time);\n"
                 "  m_own: assume property (@(posedge clk)\n"
                 "    disable iff (rst1) a |=> b) else $display(\"m_own %0d\", "
                 "$time);\n"
                 "  c_inf: cover property (@(posedge clk) a ##1 !b)\n"
                 "    $display(\"c_inf %0d\", $time);\n"
                 "  c_own: cover property (@(posedge clk)\n"
                 "    disable iff (rst1) a ##1 !b) $display(\"c_own %0d\", "
                 "$time);\n"
                 "  s_inf: cover sequence (@(posedge clk) a ##1 !b)\n"
                 "    $display(\"s_inf %0d\", $time);\n"
                 "  s_own: cover sequence (@(posedge clk)\n"
                 "    disable iff (rst1) a ##1 !b) $display(\"s_own %0d\", "
                 "$time);\n"
                 "  always @(posedge clk) begin\n"
                 "    p_inf: assert property (a |=> b)\n"
                 "      else $display(\"p_inf %0d\", $time);\n"
                 "    p_own: assert property (disable iff (rst1) a |=> b)\n"
                 "      else $display(\"p_own %0d\", $time);\n"
                 "    p_prop: assert property (p1)\n"
                 "      else $display(\"p_prop %0d\", $time);\n"
                 "  end\n"
                 "endmodule\n",
             "  kinds u(a, b, clk, rst, rst1);\n"),
      f);
  std::vector<std::string> lines;
  size_t start = 0;
  while (start < out.size()) {
    size_t end = out.find('\n', start);
    std::string line = out.substr(start, end - start);
    if (line.find("attempted") == std::string::npos &&
        line.find("$finish") == std::string::npos) {
      lines.push_back(line);
    }
    start = end + 1;
  }
  std::sort(lines.begin(), lines.end());
  std::string sorted;
  for (const auto& line : lines) sorted += line + "\n";
  return sorted;
}

TEST(DisableIffResolutionRun, EveryStatementKindResolvesItsDisableCondition) {
  EXPECT_EQ(SortedResolutionLines("  default disable iff rst;\n"),
            "c_inf 35\nc_own 15\nc_own 25\nm_inf 35\nm_own 15\nm_own 25\n"
            "p_inf 35\np_own 15\np_own 25\np_prop 15\np_prop 25\n"
            "s_inf 35\ns_own 15\ns_own 25\n");
}

TEST(DisableIffResolutionRun, WithoutADefaultNoStatementKindInfersOne) {
  EXPECT_EQ(SortedResolutionLines(""),
            "c_inf 15\nc_inf 25\nc_inf 35\nc_own 15\nc_own 25\n"
            "m_inf 15\nm_inf 25\nm_inf 35\nm_own 15\nm_own 25\n"
            "p_inf 15\np_inf 25\np_inf 35\np_own 15\np_own 25\n"
            "p_prop 15\np_prop 25\n"
            "s_inf 15\ns_inf 25\ns_inf 35\ns_own 15\ns_own 25\n");
}

}  // namespace
