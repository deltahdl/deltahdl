#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string GlitchSource(const std::string& procedures) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic en = 1, foo = 0, bar = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) bar <= ~bar;\n" +
         procedures +
         "  initial begin\n"
         "    #20 en = 0;\n"
         "    #20 $finish;\n"
         "  end\n"
         "endmodule\n";
}

const char* const kBlock2 =
    "  always_comb begin : procedural_block_2\n"
    "    p1: assert property (@(posedge clk) (const'(foo) == const'(bar)))\n"
    "      $display(\"p1 passed at %0d\", $time);\n"
    "    else $display(\"p1 failed at %0d\", $time);\n"
    "  end\n";

TEST(ProceduralAssertionGlitchRun, AFlushDropsTheGlitchOfProceduralOrder) {
  SimFixture f;
  std::string out =
      RunCapture(GlitchSource("  always_comb begin : procedural_block_1\n"
                              "    if (en) foo = bar;\n"
                              "  end\n" +
                              std::string(kBlock2)),
                 f);
  EXPECT_EQ(out,
            "p1 passed at 5\np1 passed at 5\np1 passed at 15\n"
            "p1 failed at 25\np1 passed at 35\n$finish at time 40\n");
}

TEST(ProceduralAssertionGlitchRun,
     AReactiveRegionWriteQueuesAnAttemptTooLateToPreventTheReport) {
  SimFixture f;
  std::string out = RunCapture(
      GlitchSource(std::string(kBlock2) +
                   "  program reactive_driver;\n"
                   "    initial forever @(posedge clk) if (!en) foo = bar;\n"
                   "  endprogram\n"),
      f);
  EXPECT_EQ(out,
            "p1 passed at 5\np1 failed at 5\np1 passed at 15\n"
            "p1 failed at 25\np1 passed at 25\n"
            "p1 failed at 35\np1 passed at 35\n$finish at time 40\n");
}

}  // namespace
