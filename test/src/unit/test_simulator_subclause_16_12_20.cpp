#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/property_examples.sv around one assertion:
// clk rises at 5, 15, ..., 75 so that tick n is at 10n - 5, clkev toggles
// at each rising edge, and a is high at 1, 2, 3 and 6, b at 1, 4 and 6, c
// at 2, 3 and 7, d at 2, 3, 5 and 7, e at 5 and 8 and f at 3. The clause's
// properties are declared as it writes them.
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

// The pass and fail counts at the ticks of the assertion whose whole
// property_spec is `spec`.
std::pair<uint64_t, uint64_t> CountsOfExample(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(ExamplesSource("  p: assert property (" + spec +
                                              ") passes++; else fails++;\n"),
                               f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  return {passes->value.ToUint64(), fails->value.ToUint64()};
}

// §16.12.20: rule1 requires b, c and d on consecutive ticks after a: the
// attempt from 1 holds at 3, those from 2 and 3 fail with b low, the one
// from 6 fails at 8 with d low, and the four with a low hold.
TEST(PropertyExamples, Rule1RequiresTheSequenceAfterA) {
  auto counts = CountsOfExample("rule1");
  EXPECT_EQ(counts.first, 5u);
  EXPECT_EQ(counts.second, 3u);
}

// §16.12.20: rule2 negates the sequence in the consequent, its clock the
// event clkev names and its attempts disabled while e holds: the attempt
// from 1 fails at 3, those from 2, 3, 4 and 7 hold, and the attempt from 6
// is dropped at 8 as any at 5 or 8 is not begun.
TEST(PropertyExamples, Rule2NegatesTheConsequentUnderDisableIff) {
  auto counts = CountsOfExample("rule2");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 1u);
}

// §16.12.20: rule3 requires, after a twice, c within three ticks or e a
// tick after d: the attempt from 1 holds at 3 by c, the one from 2 fails
// at 6 with neither, and the six others hold.
TEST(PropertyExamples, Rule3RequiresEitherConsequent) {
  auto counts = CountsOfExample("rule3");
  EXPECT_EQ(counts.first, 7u);
  EXPECT_EQ(counts.second, 1u);
}

// §16.12.20: rule4 requires both: the attempts from 1 and 2 fail, at 3 and
// 4, where e is low a tick after d, and the six others hold.
TEST(PropertyExamples, Rule4RequiresBothConsequents) {
  auto counts = CountsOfExample("rule4");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

// §16.12.20: rule5 splits on which of b or c is matched first after a: the
// attempts from 1 and 6 reach c and fail on f, the one from 2 reaches c and
// holds on f, the one from 3 reaches b and holds by e a tick after d, and
// the four others hold.
TEST(PropertyExamples, Rule5SplitsTheConsequentByIfElse) {
  auto counts = CountsOfExample("rule5");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

// §16.12.20: rule5a is rule5 with the then-branch an instance of rule6, and
// reads the same.
TEST(PropertyExamples, Rule5aInstantiatesRule6AsAPropertyExpression) {
  auto counts = CountsOfExample("rule5a");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

}  // namespace
