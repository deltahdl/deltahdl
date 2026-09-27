#include <gtest/gtest.h>

#include <string>

#include "driver/cli_options.h"
#include "fixture_simulator.h"
#include "helpers_command_line.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

// §31.9 (printed page 919): "Both the $setuphold and $recrem timing checks can
// accept negative values when the negative timing check option is enabled",
// and §31.9.4 (printed page 923) names "an invocation option turning off all
// timing checks" beside it. The command line had neither, so every run was the
// option-not-enabled case and a negative limit was read as 0.
TEST(NegativeTimingCheckSwitches, BothSwitchesAreRecognized) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine(
      {"--negative-timing-checks", "--no-timing-checks", "top.sv"}, opts));
  EXPECT_TRUE(opts.negative_timing_checks);
  EXPECT_TRUE(opts.no_timing_checks);
  CliOptions none;
  EXPECT_TRUE(ParseCommandLine({"top.sv"}, none));
  EXPECT_FALSE(none.negative_timing_checks);
  EXPECT_FALSE(none.no_timing_checks);
}

// Runs `src` with the two §31.9.4 options set as a run the switches selected
// is, before the design's checks are registered.
std::string RunUnder(const std::string& src, TimingCheckInvocationOptions o,
                     SimFixture& f) {
  f.ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions(o);
  return RunCapture(src, f);
}

// With the option, `$setuphold(posedge clk, d, -10, 20, n)` has its window
// shifted after the reference edge, (clk + 10, clk + 20), ends excluded: d
// changing 5 after clk is before it, 15 after is in it, 25 after is past it.
TEST(NegativeTimingCheckSwitches, NegativeSetupShiftsTheWindowAfterTheEdge) {
  SimFixture f;
  EXPECT_EQ(RunUnder("module top(\n"
                     "    output reg clk = 0,\n"
                     "    output reg d = 0);\n"
                     "  reg n = 0; integer cnt = 0;\n"
                     "  specify\n"
                     "    $setuphold(posedge clk, d, -10, 20, n);\n"
                     "  endspecify\n"
                     "  always @(n) cnt = cnt + 1;\n"
                     "  initial begin\n"
                     "    #20 clk = 1; #5 d = 1;\n"
                     "    #20 $display(\"%0d\", cnt);\n"
                     "    #5 clk = 0;\n"
                     "    #10 clk = 1; #15 d = 0;\n"
                     "    #20 $display(\"%0d\", cnt);\n"
                     "    #5 clk = 0;\n"
                     "    #10 clk = 1; #25 d = 1;\n"
                     "    #20 $display(\"%0d\", cnt);\n"
                     "  end\n"
                     "endmodule\n",
                     {true, false}, f),
            "0\n1\n1\n");
}

// A negative hold limit shifts it before the edge: `20, -10` gives
// (clk - 20, clk - 10), which d 15 before clk is in and 5 or 25 before is not.
TEST(NegativeTimingCheckSwitches, NegativeHoldShiftsTheWindowBeforeTheEdge) {
  SimFixture f;
  EXPECT_EQ(RunUnder("module top(\n"
                     "    output reg clk = 0,\n"
                     "    output reg d = 0);\n"
                     "  reg n = 0; integer cnt = 0;\n"
                     "  specify\n"
                     "    $setuphold(posedge clk, d, 20, -10, n);\n"
                     "  endspecify\n"
                     "  always @(n) cnt = cnt + 1;\n"
                     "  initial begin\n"
                     "    #15 d = 1; #15 clk = 1;\n"
                     "    #20 $display(\"%0d\", cnt);\n"
                     "    #5 clk = 0;\n"
                     "    #20 d = 0; #5 clk = 1;\n"
                     "    #20 $display(\"%0d\", cnt);\n"
                     "    #5 clk = 0;\n"
                     "    #5 d = 1; #25 clk = 1;\n"
                     "    #20 $display(\"%0d\", cnt);\n"
                     "  end\n"
                     "endmodule\n",
                     {true, false}, f),
            "1\n1\n1\n");
}

// §31.9.1 (printed page 922): "The setup time of -7 (the larger in absolute
// value) creates a delay of 7 for dCLK", so under the option dclk rises 7
// after clk and samples through dd the d that changed 2 after clk. Without the
// option the two are copies and dclk rises with clk.
TEST(NegativeTimingCheckSwitches,
     DelayedReferenceLagsByTheLargestNegativeSetup) {
  const std::string kDesign =
      "module top(output reg q, output reg clk = 0, output reg d = 0);\n"
      "  reg n = 0; integer t = 0;\n"
      "  specify\n"
      "    $setuphold(posedge clk, posedge d, -3, 8, n, , , dclk, dd);\n"
      "    $setuphold(posedge clk, negedge d, -7, 13, n, , , dclk, dd);\n"
      "  endspecify\n"
      "  always @(posedge dclk) begin q <= dd; t = $time; end\n"
      "  initial begin\n"
      "    #20 clk = 1;\n"
      "    #2 d = 1;\n"
      "    #20 $display(\"%b %0d\", q, t);\n"
      "  end\n"
      "endmodule\n";
  SimFixture on;
  EXPECT_EQ(RunUnder(kDesign, {true, false}, on), "1 27\n");
  SimFixture off;
  EXPECT_EQ(RunUnder(kDesign, {false, false}, off), "0 20\n");
}

// §31.9.4's other option turns every timing check off: the violation d makes
// 2 before clk reports nothing and leaves the notifier where it was.
TEST(NegativeTimingCheckSwitches, AllChecksOffReportsNothing) {
  SimFixture f;
  EXPECT_EQ(RunUnder("module top(\n"
                     "    output reg clk = 0,\n"
                     "    output reg d = 0);\n"
                     "  reg n = 0; integer cnt = 0;\n"
                     "  specify\n"
                     "    $setuphold(posedge clk, d, 5, 5, n);\n"
                     "  endspecify\n"
                     "  always @(n) cnt = cnt + 1;\n"
                     "  initial begin\n"
                     "    #10 d = 1; #2 clk = 1;\n"
                     "    #5 $display(\"%0d\", cnt);\n"
                     "  end\n"
                     "endmodule\n",
                     {false, true}, f),
            "0\n");
}

}  // namespace
