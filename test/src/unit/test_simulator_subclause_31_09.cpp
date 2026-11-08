#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "driver/cli_options.h"
#include "fixture_simulator.h"
#include "helpers_command_line.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"
#include "simulator/sdf_parser.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

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

std::string RunUnder(const std::string& src, TimingCheckInvocationOptions o,
                     SimFixture& f) {
  f.ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions(o);
  return PreprocessAndCapture(src, f);
}

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

TEST(NegativeTimingCheckSwitches, LimitSumIsCountedInUnitsOfTheFullPrecision) {
  SimFixture f;
  RunUnder(
      "`timescale 1ns/10ps\n"
      "module top(output reg clk = 0, output reg d = 0);\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, -1, 1.01);\n"
      "  endspecify\n"
      "endmodule\n",
      {true, false}, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sum to 1 in units of simulation precision", 4,
                            "31.3.3"));
}

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

TEST(NegativeTimingCheckSwitches,
     DelayedSignalsTakeTheLeastDelaysLeavingEveryLimitOneUnit) {
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

TEST(NegativeTimingCheckSwitches, SetupOnADelayedClockTogglesAtTheDelayedEdge) {
  SimFixture f;
  EXPECT_EQ(RunUnder("`timescale 1ns/1ns\n"
                     "module top(output reg clk = 0, output reg d = 0,\n"
                     "           output reg e = 0);\n"
                     "  reg n = 0;\n"
                     "  specify\n"
                     "    $setuphold(posedge clk, d, -10, 20);\n"
                     "    $setup(e, posedge clk, 5, n);\n"
                     "  endspecify\n"
                     "  always @(n) $display(\"%0d\", $time);\n"
                     "  initial begin\n"
                     "    #100 e = 1;\n"
                     "    #2 clk = 1;\n"
                     "  end\n"
                     "endmodule\n",
                     {true, false}, f),
            "113\n");
}

TEST(NegativeTimingCheckSwitches, HoldAdjustedBelowZeroIsZeroedWithAWarning) {
  SimFixture f;
  EXPECT_EQ(RunUnder("`timescale 1ns/1ns\n"
                     "module top(output reg clk = 0, output reg d = 0,\n"
                     "           output reg e = 0);\n"
                     "  reg n = 0;\n"
                     "  specify\n"
                     "    $setuphold(posedge clk, d, -10, 20);\n"
                     "    $hold(posedge clk, e, 5, n);\n"
                     "  endspecify\n"
                     "  always @(n) $display(\"%0d\", $time);\n"
                     "  initial begin\n"
                     "    #100 clk = 1;\n"
                     "    #2 e = 1;\n"
                     "  end\n"
                     "endmodule\n",
                     {true, false}, f),
            "");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "is no longer positive and is set to 0", 7,
                              "31.9.1"));
}

TEST(NegativeTimingCheckSwitches, WidthOnADelayedClockReportsAtTheDelayedEdge) {
  SimFixture f;
  EXPECT_EQ(RunUnder("`timescale 1ns/1ns\n"
                     "module top(output reg clk = 0, output reg d = 0);\n"
                     "  reg n = 0;\n"
                     "  specify\n"
                     "    $setuphold(posedge clk, d, -10, 20);\n"
                     "    $width(posedge clk, 10, 0, n);\n"
                     "  endspecify\n"
                     "  always @(n) $display(\"%0d\", $time);\n"
                     "  initial begin\n"
                     "    #100 clk = 1;\n"
                     "    #5 clk = 0;\n"
                     "  end\n"
                     "endmodule\n",
                     {true, false}, f),
            "116\n");
}

TEST(NegativeTimingCheckSwitches, NochangeOnADelayedClockReportsAtItsClose) {
  SimFixture f;
  EXPECT_EQ(RunUnder("`timescale 1ns/1ns\n"
                     "module top(output reg clk = 0, output reg d = 0,\n"
                     "           output reg e = 0);\n"
                     "  reg n = 0;\n"
                     "  specify\n"
                     "    $setuphold(posedge clk, d, -10, 20);\n"
                     "    $nochange(posedge clk, e, 0, 0, n);\n"
                     "  endspecify\n"
                     "  always @(n) $display(\"%0d\", $time);\n"
                     "  initial begin\n"
                     "    #100 clk = 1;\n"
                     "    #10 e = 1;\n"
                     "    #10 clk = 0;\n"
                     "  end\n"
                     "endmodule\n",
                     {true, false}, f),
            "131\n");
}

TEST(NegativeTimingCheckSwitches, SkewKeepsTheUndelayedSignals) {
  SimFixture f;
  EXPECT_EQ(RunUnder("`timescale 1ns/1ns\n"
                     "module top(output reg clk = 0, output reg d = 0,\n"
                     "           output reg e = 0);\n"
                     "  reg n = 0;\n"
                     "  specify\n"
                     "    $setuphold(posedge clk, d, -10, 20);\n"
                     "    $skew(posedge clk, posedge e, 3, n);\n"
                     "  endspecify\n"
                     "  always @(n) $display(\"%0d\", $time);\n"
                     "  initial begin\n"
                     "    #100 clk = 1;\n"
                     "    #5 e = 1;\n"
                     "  end\n"
                     "endmodule\n",
                     {true, false}, f),
            "105\n");
}

SpecifyManager& ManagerWithClkDelayed(const std::string& check, SimFixture& f) {
  RunUnder(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d = 0,\n"
      "           output reg e = 0);\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, -10, 20);\n"
      "    " +
          check +
          "\n"
          "  endspecify\n"
          "endmodule\n",
      {true, false}, f);
  return *f.ctx.GetSpecifyManager();
}

std::vector<std::string> AnnotateOntoTop(const std::string& entry,
                                         SpecifyManager& mgr) {
  SdfFile file;
  EXPECT_TRUE(
      ParseSdf("(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) "
               "(TIMINGCHECK " +
                   entry + ")))",
               file));
  return AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, {}, "top").warnings;
}

const TimingCheckEntry& CheckOfKind(const SpecifyManager& mgr,
                                    TimingCheckKind kind) {
  for (const TimingCheckEntry& e : mgr.GetTimingChecks()) {
    if (e.kind == kind) return e;
  }
  return mgr.GetTimingChecks().front();
}

TEST(NegativeTimingCheckSwitches, AnnotatedLimitOfADelayedCheckIsAdjusted) {
  SimFixture f;
  SpecifyManager& mgr = ManagerWithClkDelayed("$setup(e, posedge clk, 5);", f);
  AnnotateOntoTop("(SETUP e (posedge clk) (7))", mgr);
  EXPECT_EQ(CheckOfKind(mgr, TimingCheckKind::kSetup).limit, 18u);
}

TEST(NegativeTimingCheckSwitches, AnnotatedLimitAdjustedBelowZeroIsZeroed) {
  SimFixture f;
  SpecifyManager& mgr = ManagerWithClkDelayed("$hold(posedge clk, e, 5);", f);
  const std::vector<std::string> kWarnings =
      AnnotateOntoTop("(HOLD e (posedge clk) (8))", mgr);
  EXPECT_EQ(CheckOfKind(mgr, TimingCheckKind::kHold).limit, 0u);
  ASSERT_EQ(kWarnings.size(), 1u);
  EXPECT_NE(kWarnings[0].find("is no longer positive and is set to 0"),
            std::string::npos);
}

TEST(NegativeTimingCheckSwitches, AnnotatedNochangeOffsetsAreMoved) {
  SimFixture f;
  SpecifyManager& mgr =
      ManagerWithClkDelayed("$nochange(posedge clk, e, 0, 0);", f);
  AnnotateOntoTop("(NOCHANGE (posedge clk) e (3) (4))", mgr);
  const TimingCheckEntry& check = CheckOfKind(mgr, TimingCheckKind::kNochange);
  EXPECT_EQ(check.start_edge_offset, 14);
  EXPECT_EQ(check.end_edge_offset, -7);
}

}  // namespace
