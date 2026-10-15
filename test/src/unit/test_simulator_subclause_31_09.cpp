#include <gtest/gtest.h>

#include <string>

#include "driver/cli_options.h"
#include "fixture_simulator.h"
#include "helpers_command_line.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

// §31.9 (printed page 919): with the negative timing check option on,
// $setuphold and $recrem may take negative values, and §31.9.4 (printed page
// 923) names beside it an invocation option that turns every timing check off.
// The command line had neither, so every run was the option-not-enabled case
// and a negative limit was read as 0.
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

// Runs `src`, preprocessed so that its `timescale sets the precision the
// delayed signals' delays are counted in, with the two §31.9.4 options set as a
// run the switches selected is, before the design's checks are registered.
std::string RunUnder(const std::string& src, TimingCheckInvocationOptions o,
                     SimFixture& f) {
  f.ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions(o);
  return PreprocessAndCapture(src, f);
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

// §31.9.1 (printed page 922): the setup time of -7, the larger in magnitude,
// gives dCLK a delay of 7 -- 7.1 on a 100 ps precision, the least delay that
// leaves the adjusted setup limit one unit of precision -- so under the option
// dclk rises 7.1 after clk, which $time reads as 27, and samples through dd the
// d that changed 2 after clk. Without the option the two are copies and dclk
// rises with clk.
TEST(NegativeTimingCheckSwitches,
     DelayedReferenceLagsByTheLargestNegativeSetup) {
  const std::string kDesign =
      "`timescale 1ns/100ps\n"
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

// §31.3.3 (printed page 901): with a limit negative, a $setuphold's two limits
// sum to more than one unit of simulation precision. -4 and 5 sum to 1 under a
// 1 ns precision, which is not more.
TEST(NegativeTimingCheckSwitches, SetupholdLimitsSummingToOneUnitAreReported) {
  SimFixture f;
  RunUnder(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d = 0);\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, -4, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      {true, false}, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sum to 1 in units of simulation precision", 4,
                            "31.3.3"));
}

// Two units are more than one, so -4 and 6 meet the restriction.
TEST(NegativeTimingCheckSwitches, SetupholdLimitsSummingToTwoUnitsAreAccepted) {
  SimFixture f;
  RunUnder(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d = 0);\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, -4, 6);\n"
      "  endspecify\n"
      "endmodule\n",
      {true, false}, f);
  EXPECT_EQ(FindDiag(f, "in units of simulation precision"), nullptr);
}

// §31.3.6 (printed page 904) puts the same restriction on $recrem's recovery
// and removal limits, which -10 and 5 break.
TEST(NegativeTimingCheckSwitches, RecremLimitsSummingBelowOneUnitAreReported) {
  SimFixture f;
  RunUnder(
      "`timescale 1ns/1ns\n"
      "module top(output reg clr = 0, output reg clk = 0);\n"
      "  specify\n"
      "    $recrem(posedge clr, posedge clk, -10, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      {true, false}, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sum to -5 in units of simulation precision", 4,
                            "31.3.6"));
}

// §31.9.1's Figure 31-6 (printed page 923) gives the delays of its three
// checks' delayed signals on a 10 ps precision: 10.01 for cp, 0 for d, 20.02
// for ti and 2.02 for te, the least delays that leave every adjusted limit at
// least one unit of precision. Each delayed copy rises that long after the
// original, which all rise at 100.
TEST(NegativeTimingCheckSwitches, DelayedSignalsTakeFigure31_6Delays) {
  SimFixture f;
  EXPECT_EQ(
      RunUnder("`timescale 1ns/10ps\n"
               "module top(output reg cp = 0, output reg d = 0,\n"
               "           output reg ti = 0, output reg te = 0);\n"
               "  specify\n"
               "    $setuphold(posedge cp, d, -10, 20, , , , dcp, dd);\n"
               "    $setuphold(posedge cp, ti, 20, -10, , , , dcp, dti);\n"
               "    $setuphold(posedge cp, te, -4, 8, , , , dcp, dte);\n"
               "  endspecify\n"
               "  always @(posedge dcp) $display(\"dcp %0.2f\", $realtime);\n"
               "  always @(posedge dd) $display(\"dd %0.2f\", $realtime);\n"
               "  always @(posedge dti) $display(\"dti %0.2f\", $realtime);\n"
               "  always @(posedge dte) $display(\"dte %0.2f\", $realtime);\n"
               "  initial begin\n"
               "    #100 cp = 1; d = 1; ti = 1; te = 1;\n"
               "  end\n"
               "endmodule\n",
               {true, false}, f),
      "dd 100.00\ndte 102.02\ndcp 110.01\ndti 120.02\n");
}

// §31.9.1 (printed page 921): a lags b by more than 10 in the first check and b
// lags a by more than 10 in the second, which no delays satisfy. The run warns
// and sets the least negative limit to 0, the first check's -10 where the two
// tie, after which b lags a by 11 and a does not lag at all.
TEST(NegativeTimingCheckSwitches,
     InconsistentLimitsWarnAndZeroTheLeastNegative) {
  SimFixture f;
  EXPECT_EQ(RunUnder("`timescale 1ns/1ns\n"
                     "module top(output reg a = 0, output reg b = 0);\n"
                     "  specify\n"
                     "    $setuphold(posedge a, b, -10, 12, , , , da, db);\n"
                     "    $setuphold(posedge b, a, -10, 12);\n"
                     "  endspecify\n"
                     "  always @(posedge da) $display(\"da %0d\", $time);\n"
                     "  always @(posedge db) $display(\"db %0d\", $time);\n"
                     "  initial begin\n"
                     "    #10 a = 1; b = 1;\n"
                     "  end\n"
                     "endmodule\n",
                     {true, false}, f),
            "da 10\ndb 21\n");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "no consistent delays", 4,
                              "31.9.1"));
}

// §31.9.3 (printed page 923): the check is evaluated on the delayed signals, so
// the notifier toggles when they violate. Under Figure 31-6's delays te
// changing at 505, inside the (504, 508) window cp rising at 500 sets, reaches
// the delayed te at 507.02, and the violation is detected when the delayed cp
// rises at 510.01.
TEST(NegativeTimingCheckSwitches, NotifierTogglesWhenTheDelayedSignalsViolate) {
  SimFixture f;
  EXPECT_EQ(RunUnder("`timescale 1ns/10ps\n"
                     "module top(output reg cp = 0, output reg d = 0,\n"
                     "           output reg ti = 0, output reg te = 0);\n"
                     "  reg n = 0;\n"
                     "  specify\n"
                     "    $setuphold(posedge cp, d, -10, 20);\n"
                     "    $setuphold(posedge cp, ti, 20, -10);\n"
                     "    $setuphold(posedge cp, te, -4, 8, n);\n"
                     "  endspecify\n"
                     "  always @(n) $display(\"%0.2f\", $realtime);\n"
                     "  initial begin\n"
                     "    #500 cp = 1;\n"
                     "    #5 te = 1;\n"
                     "  end\n"
                     "endmodule\n",
                     {true, false}, f),
            "510.01\n");
}

}  // namespace
