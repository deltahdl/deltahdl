#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(SemanticLeadingClockRun, IdenticalLeadingClocksRunAsOne) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic clk1 = 0;\n"
      "  wire clk2;\n"
      "  logic a = 1, b = 0, c = 0;\n"
      "  assign clk2 = clk1;\n"
      "  always #5 clk1 = ~clk1;\n"
      "  a2: assert property (@(clk1) a and @(clk1) b)\n"
      "    $display(\"a2 at %0d\", $time); else;\n"
      "  always @(posedge clk1) begin\n"
      "    a4: assert property (a and @(posedge clk1) c)\n"
      "      $display(\"a4 at %0d\", $time); else;\n"
      "  end\n"
      "  c1: cover property (@(posedge clk1) a ##1 @(negedge clk1) c)\n"
      "    $display(\"c1 at %0d\", $time);\n"
      "  initial begin\n"
      "    #12 b = 1;\n"
      "    #10 b = 0; c = 1;\n"
      "    #10 c = 0;\n"
      "    #8 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "a2 at 15\n"
            "a2 at 20\n"
            "a4 at 25\n"
            "c1 at 30\n"
            "$finish at time 40\n");
  const auto& results = f.ctx.ConcurrentCovers().Results();
  ASSERT_EQ(results.size(), 1u);
  EXPECT_EQ(results[0].attempted, 4u);
  EXPECT_EQ(results[0].succeeded, 1u);
}

}  // namespace
