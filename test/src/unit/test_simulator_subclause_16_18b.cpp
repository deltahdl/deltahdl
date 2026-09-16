#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's module A around the assertion given, driven as its Figure
// 16-17 draws: clk rises at 5, 15, 25, 35, 45 and 55, a rises at 20 and
// falls at 40, and the run ends at 60, so an assertion of a on posedge clk
// passes at 25 and 35 and fails at the other edges.
std::string Design(const std::string& assertion) {
  return "module A(input logic clk, input logic a);\n"
         "  clocking cb_with_input @(posedge clk);\n"
         "    input a;\n"
         "    property p1;\n"
         "      a;\n"
         "    endproperty\n"
         "  endclocking\n"
         "  clocking cb_without_input @(posedge clk);\n"
         "    property p1;\n"
         "      a;\n"
         "    endproperty\n"
         "  endclocking\n"
         "  property p1;\n"
         "    @(posedge clk) a;\n"
         "  endproperty\n"
         "  property p2;\n"
         "    @(posedge clk) cb_with_input.a;\n"
         "  endproperty\n" +
         assertion +
         "endmodule\n"
         "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  A u1(clk, a);\n"
         "  initial begin\n"
         "    #20 a = 1;\n"
         "    #20 a = 0;\n"
         "    #20 $finish;\n"
         "  end\n"
         "endmodule\n";
}

std::string Passes(const std::string& assertion) {
  SimFixture f;
  return RunCapture(Design(assertion), f);
}

// §16.18: a clocking block variable used in a concurrent assertion is
// sampled only in the clocking block, at posedge clk with the default
// input skew, where the assertion samples the module's a as well, so the
// clause's a3, asserting cb_with_input.a through p2, passes where its a1,
// asserting a through p1, does: at 25 and 35.
TEST(ClockingBlockAssertionRun, AClockingBlockVariableReadsTheBlocksSample) {
  const std::string kExpected =
      "passed at 25\npassed at 35\n$finish at time 60\n";
  EXPECT_EQ(Passes("  a1: assert property (p1) $display(\"passed at %0d\", "
                   "$time); else;\n"),
            kExpected);
  EXPECT_EQ(Passes("  a3: assert property (p2) $display(\"passed at %0d\", "
                   "$time); else;\n"),
            kExpected);
}

// §16.18: the clause's a2 and a4 instantiate the p1 of each clocking
// block, cb_with_input's asserting its clocking block variable a and
// cb_without_input's the module's a, and both pass at 25 and 35 as a1
// does, the four being equivalent.
TEST(ClockingBlockAssertionRun, ThePropertiesOfBothBlocksAreEquivalent) {
  const std::string kExpected =
      "passed at 25\npassed at 35\n$finish at time 60\n";
  EXPECT_EQ(Passes("  a2: assert property (cb_with_input.p1)\n"
                   "    $display(\"passed at %0d\", $time); else;\n"),
            kExpected);
  EXPECT_EQ(Passes("  a4: assert property (cb_without_input.p1)\n"
                   "    $display(\"passed at %0d\", $time); else;\n"),
            kExpected);
}

}  // namespace
