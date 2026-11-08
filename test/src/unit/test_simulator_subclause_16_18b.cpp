#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(ClockingBlockAssertionRun, ACheckerFormalBoundToABlockVariableReadsIt) {
  SimFixture f;
  std::string out = RunCapture(
      "checker chk(logic x, logic c);\n"
      "  a1: assert property (@(posedge c) x)\n"
      "    $display(\"passed at %0d\", $time); else;\n"
      "endchecker\n" +
          Design("  chk k(cb_with_input.a, clk);\n"),
      f);
  EXPECT_EQ(out, "passed at 25\npassed at 35\n$finish at time 60\n");
}

}  // namespace
