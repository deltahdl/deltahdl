#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A module around the procedures given, as
// test/src/e2e/procedural_assertion_disable.sv is: clk rises at 5, 15, ...,
// 45 and is the default clocking, a and b are 1 throughout, go is 1 from 10
// and 2 from 20, go2 is 1 from 30 and 2 from 40, clear_b2 is 1 from 30 to
// 41, and the run ends at 50.
std::string DisableSource(const std::string& procedures) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 1, b = 1;\n"
         "  int go = 0, go2 = 0;\n"
         "  logic clear_b2 = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  default clocking @(posedge clk); endclocking\n" +
         procedures +
         "  initial begin\n"
         "    #10 go = 1;\n"
         "    #10 go = 2;\n"
         "    #10 go2 = 1;\n"
         "    clear_b2 = 1;\n"
         "    #10 go2 = 2;\n"
         "    #1 clear_b2 = 0;\n"
         "    #9 $finish;\n"
         "  end\n"
         "endmodule\n";
}

// §16.14.6.4: a disable naming a specific procedural concurrent assertion
// clears its pending instances and leaves the others', and reaches no
// matured instance: b1 queues a1 and a2 at 10 and disables a1 after a
// delay, when both have matured, so both pass at 15; at 20 it disables a1
// in the same step, so a2 alone passes at 25.
TEST(DisablingProceduralAssertionsRun,
     ASpecificDisableClearsThatAssertionsPendingInstancesAlone) {
  SimFixture f;
  std::string out =
      RunCapture(DisableSource("  always @(go) begin : b1\n"
                               "    a1: assert property (const'(a))\n"
                               "      $display(\"a1 passed at %0d\", $time);\n"
                               "    a2: assert property (const'(b))\n"
                               "      $display(\"a2 passed at %0d\", $time);\n"
                               "    if (go == 2) disable a1;\n"
                               "    else begin\n"
                               "      #1 disable a1;\n"
                               "    end\n"
                               "  end\n"),
                 f);
  EXPECT_EQ(out,
            "a1 passed at 15\na2 passed at 15\na2 passed at 25\n"
            "$finish at time 50\n");
}

// §16.14.6.4: a disable applied to the outermost scope of a procedure with
// a pending queue flushes the queue, and reaches no matured instance: b3
// disables b2 at 30 in the step b2 queued a3 and a4, so nothing passes at
// 35, and at 41, a step after b2 queued them, so both pass at 45.
TEST(DisablingProceduralAssertionsRun,
     ADisableOfTheOutermostScopeFlushesThePendingQueue) {
  SimFixture f;
  std::string out =
      RunCapture(DisableSource("  always @(go2) begin : b2\n"
                               "    a3: assert property (const'(a))\n"
                               "      $display(\"a3 passed at %0d\", $time);\n"
                               "    a4: assert property (const'(b))\n"
                               "      $display(\"a4 passed at %0d\", $time);\n"
                               "  end\n"
                               "  always @(clear_b2) begin : b3\n"
                               "    disable b2;\n"
                               "  end\n"),
                 f);
  EXPECT_EQ(out, "a3 passed at 45\na4 passed at 45\n$finish at time 50\n");
}

}  // namespace
