#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string ExamplesSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic clkev = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c, d, e, f;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  always @(posedge clk) clkev <= ~clkev;\n"
         "  assign a = tick inside {1, 2, 3, 6};\n"
         "  assign b = tick inside {1, 4, 6};\n"
         "  assign c = tick inside {2, 3, 7};\n"
         "  assign d = tick inside {2, 3, 5, 7};\n"
         "  assign e = tick inside {5, 8};\n"
         "  assign f = tick inside {3};\n"
         "  property rule1;\n"
         "    @(posedge clk) a |-> b ##1 c ##1 d;\n"
         "  endproperty\n"
         "  property rule2;\n"
         "    @(clkev) disable iff (e) a |-> not (b ##1 c ##1 d);\n"
         "  endproperty\n"
         "  property rule3;\n"
         "    @(posedge clk) a[*2] |-> ((##[1:3] c) or (d |=> e));\n"
         "  endproperty\n"
         "  property rule4;\n"
         "    @(posedge clk) a[*2] |-> ((##[1:3] c) and (d |=> e));\n"
         "  endproperty\n"
         "  property rule5;\n"
         "    @(posedge clk)\n"
         "    a ##1 (b || c)[->1] |->\n"
         "      if (b)\n"
         "        (##1 d |-> e)\n"
         "      else\n"
         "        f;\n"
         "  endproperty\n"
         "  property rule6(x, y);\n"
         "    ##1 x |-> y;\n"
         "  endproperty\n"
         "  property rule5a;\n"
         "    @(posedge clk)\n"
         "    a ##1 (b || c)[->1] |->\n"
         "      if (b)\n"
         "        rule6(d, e)\n"
         "      else\n"
         "        f;\n"
         "  endproperty\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

std::pair<uint64_t, uint64_t> CountsOfExample(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(ExamplesSource("  p: assert property (" + spec +
                                              ") passes++; else fails++;\n"),
                               f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  return {passes->value.ToUint64(), fails->value.ToUint64()};
}

TEST(PropertyExamples, Rule1RequiresTheSequenceAfterA) {
  auto counts = CountsOfExample("rule1");
  EXPECT_EQ(counts.first, 5u);
  EXPECT_EQ(counts.second, 3u);
}

TEST(PropertyExamples, Rule2NegatesTheConsequentUnderDisableIff) {
  auto counts = CountsOfExample("rule2");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(PropertyExamples, Rule3RequiresEitherConsequent) {
  auto counts = CountsOfExample("rule3");
  EXPECT_EQ(counts.first, 7u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(PropertyExamples, Rule4RequiresBothConsequents) {
  auto counts = CountsOfExample("rule4");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

TEST(PropertyExamples, Rule5SplitsTheConsequentByIfElse) {
  auto counts = CountsOfExample("rule5");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

TEST(PropertyExamples, Rule5aInstantiatesRule6AsAPropertyExpression) {
  auto counts = CountsOfExample("rule5a");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

}  // namespace
