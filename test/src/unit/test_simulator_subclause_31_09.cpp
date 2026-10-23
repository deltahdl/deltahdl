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

// The unit is the precision's, magnitude and all: -1 and 1.01 sum to one unit
// of a 10 ps precision, which is ten of its 1 ps ticks, and is not more.
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

// §31.9.1 (printed page 921): every check naming a signal that has a delayed
// copy is evaluated on that copy, a $setup with no negative limit of its own
// among them. The $setuphold delays clk by 11 and e not at all, so the $setup
// limit of 5 is adjusted to 16 and the check sees e change at 100 and the
// delayed clk rise at 113, 13 apart and inside it. The notifier toggles then,
// not at 102 when the undelayed clk rose.
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

// The same delays adjust a $hold limit of 5 to 5 - 11, which is not positive,
// so §31.9.1 sets it to 0 with a warning, and a $hold of limit 0 reports
// nothing: e changing 2 after clk, a violation of the declared limit, toggles
// no notifier.
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

// $width watches one signal, whose edges are delayed alike, so its limit is
// not adjusted, but it is evaluated on the delayed clk: the pulse from 100 to
// 105 is too narrow, and the violation is seen at the delayed falling edge,
// 116.
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

// A $nochange's offsets move with the delays as a limit does, so on the
// delayed clk, high from 111 to 131, its window still covers 100 to 120 and e
// changing at 110 violates it; the violation is seen when the delayed clk
// falls and closes the window, at 131.
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

// §31.9.1 keeps $skew on the undelayed signals: e rising 5 after clk exceeds
// the limit of 3 at 105, though the delayed clk, rising at 111, would put e
// before it.
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

// The checks a run of `check` beside $setuphold(posedge clk, d, -10, 20) left
// registered, under the option that delays clk by 11 and e not at all.
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

// §32.4.2's TIMINGCHECK entry `entry`, annotated onto the top's checks.
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

// §31.9.1 adjusts whatever limit the check carries, an annotated one as much as
// a declared one: the $setup is evaluated on the delayed clk, so the annotated
// 7 is applied as 7 + 11.
TEST(NegativeTimingCheckSwitches, AnnotatedLimitOfADelayedCheckIsAdjusted) {
  SimFixture f;
  SpecifyManager& mgr = ManagerWithClkDelayed("$setup(e, posedge clk, 5);", f);
  AnnotateOntoTop("(SETUP e (posedge clk) (7))", mgr);
  EXPECT_EQ(CheckOfKind(mgr, TimingCheckKind::kSetup).limit, 18u);
}

// An annotated $hold limit of 8 adjusts to 8 - 11, which is not positive, so it
// is set to 0 and the annotation warns.
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

// $nochange's annotated offsets move as its declared ones do: the start offset
// by 11 and the end offset by -11.
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
