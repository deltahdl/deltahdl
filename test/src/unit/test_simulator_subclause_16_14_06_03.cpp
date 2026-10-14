#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A module around the procedures given, as
// test/src/e2e/procedural_assertion_glitches.sv is: clk rises at 5, 15, 25
// and 35, bar toggles at each posedge, en is 1 until 20, and the run ends
// at 40.
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

// §16.14.6.3: the clause's procedural_block_2 may run twice in the Active
// region of a posedge, on the change of bar and again after
// procedural_block_1 assigns it to foo, and the instance the first run
// queued on the stale foo is flushed by the second, so no glitch is
// reported: p1 passes at 5, for the instance of 0 and for the step's own,
// and at 15; and with en 0 from 20 nothing updates foo, so p1 fails at 25,
// where bar rose, and passes at 35, where it fell back to foo.
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

// §16.14.6.3: with foo assigned from bar in the Reactive region instead,
// once en is 0, the Observed region has already matured and failed the
// instance queued on the change of bar, and the instance queued in the
// Active region that follows the assignment begins its attempt in the same
// time step and passes, too late to prevent the report; while en is 1
// nothing updates foo, so the instance of 0 passes at 5 and the step's own
// fails there, and 15's passes with bar back at 0.
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
