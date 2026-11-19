#include <gtest/gtest.h>

#include <cstddef>
#include <fstream>
#include <ios>
#include <set>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

std::string RunWithTheOption(const std::string& src, SimFixture& f) {
  f.ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions({true, false});
  return PreprocessAndCapture(src, f);
}

std::string RunWithTheOption(const std::string& src) {
  SimFixture f;
  return RunWithTheOption(src, f);
}

std::string WindowDesign(const std::string& timescale, const std::string& check,
                         const std::string& data_at) {
  return "`timescale " + timescale +
         "\n"
         "module top(output reg r = 0, output reg d = 0);\n"
         "  reg n = 0; integer cnt = 0;\n"
         "  specify\n"
         "    " +
         check +
         "\n"
         "  endspecify\n"
         "  always @(n) cnt = cnt + 1;\n"
         "  initial begin\n"
         "    fork #100 r = 1; #" +
         data_at +
         " d = 1; join\n"
         "    #50 $display(\"%0d\", cnt);\n"
         "  end\n"
         "endmodule\n";
}

std::string TogglesForDataAt(const std::string& check,
                             const std::vector<int>& offsets) {
  std::string out;
  for (int offset : offsets) {
    out += RunWithTheOption(
        WindowDesign("1ns/1ns", check, std::to_string(100 + offset)));
  }
  return out;
}

TEST(NegativeTimingCheckRun, SetupholdEndPointsOfANegativeWindowDoNotViolate) {
  EXPECT_EQ(
      TogglesForDataAt("$setuphold(posedge r, d, -10, 20, n);", {10, 15, 20}),
      "0\n1\n0\n");
}

TEST(NegativeTimingCheckRun, SetupholdEndPointsOfANegativeHoldDoNotViolate) {
  EXPECT_EQ(TogglesForDataAt("$setuphold(posedge r, d, 20, -10, n);",
                             {-20, -15, -10}),
            "0\n1\n0\n");
}

TEST(NegativeTimingCheckRun, RecremEndPointsOfANegativeRemovalDoNotViolate) {
  EXPECT_EQ(
      TogglesForDataAt("$recrem(posedge r, posedge d, 10, -5, n);", {5, 7, 10}),
      "0\n1\n0\n");
}

TEST(NegativeTimingCheckRun, RecremEndPointsOfANegativeRecoveryDoNotViolate) {
  EXPECT_EQ(TogglesForDataAt("$recrem(posedge r, posedge d, -5, 10, n);",
                             {-10, -7, -5}),
            "0\n1\n0\n");
}

TEST(NegativeTimingCheckRun, WindowOfTwoPrecisionUnitsViolatesInside) {
  EXPECT_EQ(TogglesForDataAt("$setuphold(posedge r, d, -4, 6, n);", {4, 5, 6}),
            "0\n1\n0\n");
}

TEST(NegativeTimingCheckRun, WindowWidthIsCountedInPrecisionUnits) {
  std::string out;
  for (const char* data_at : {"104.0", "104.1", "104.2"}) {
    out += RunWithTheOption(WindowDesign(
        "1ns/100ps", "$setuphold(posedge r, d, -4, 4.2, n);", data_at));
  }
  EXPECT_EQ(out, "0\n1\n0\n");
}

std::string AnnotatedWindowDesign(const std::string& sdf_limits,
                                  const std::string& data_at) {
  const std::string kPath = "/tmp/delta_c31_09_01b_window.sdf";
  std::ofstream(kPath, std::ios::trunc)
      << "(DELAYFILE (TIMESCALE 1ns) (CELL (CELLTYPE \"top\") (INSTANCE top) "
         "(TIMINGCHECK (SETUPHOLD d (posedge r) " +
             sdf_limits + "))))";
  return "`timescale 1ns/1ns\n"
         "module top(output reg r = 0, output reg d = 0);\n"
         "  reg n = 0; integer cnt = 0;\n"
         "  specify\n"
         "    $setuphold(posedge r, d, -10, 20, n);\n"
         "  endspecify\n"
         "  always @(n) cnt = cnt + 1;\n"
         "  initial $sdf_annotate(\"" +
         kPath +
         "\", top);\n"
         "  initial begin\n"
         "    fork #100 r = 1; #" +
         data_at +
         " d = 1; join\n"
         "    #50 $display(\"%0d\", cnt);\n"
         "  end\n"
         "endmodule\n";
}

TEST(NegativeTimingCheckRun, AnnotatedWindowOfOneUnitNeverViolates) {
  std::string out;
  for (const char* data_at : {"104", "105"}) {
    out += RunWithTheOption(AnnotatedWindowDesign("(-4) (5)", data_at));
  }
  EXPECT_EQ(out, "0\n0\n");
}

TEST(NegativeTimingCheckRun, AnnotatedWindowOfTwoUnitsViolatesInside) {
  EXPECT_EQ(RunWithTheOption(AnnotatedWindowDesign("(-4) (6)", "105")), "1\n");
}

std::string LatchedValueDesign(int data_at) {
  return "`timescale 1ns/1ns\n"
         "module top(output reg q = 0, output reg clk = 0, output reg d = 0);\n"
         "  specify\n"
         "    $setuphold(posedge clk, d, -10, 20, , , , dclk, dd);\n"
         "  endspecify\n"
         "  always @(posedge dclk) q <= dd;\n"
         "  initial begin\n"
         "    fork #20 clk = 1; #" +
         std::to_string(data_at) +
         " d = 1; join\n"
         "    #40 $display(\"%b\", q);\n"
         "  end\n"
         "endmodule\n";
}

TEST(NegativeTimingCheckRun, ChangeAtTheLowerEndPointIsLatched) {
  EXPECT_EQ(RunWithTheOption(LatchedValueDesign(30)), "1\n");
}

TEST(NegativeTimingCheckRun, ChangeInsideOrAfterTheWindowIsNotLatched) {
  std::string out;
  for (int data_at : {35, 40, 45}) {
    out += RunWithTheOption(LatchedValueDesign(data_at));
  }
  EXPECT_EQ(out, "0\n0\n0\n");
}

std::string DelayedCopyTimes(const std::string& check) {
  return RunWithTheOption(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d = 0);\n"
      "  specify\n"
      "    " +
      check +
      "\n"
      "  endspecify\n"
      "  always @(posedge dclk) $display(\"dclk %0d\", $time);\n"
      "  always @(posedge dd) $display(\"dd %0d\", $time);\n"
      "  initial begin\n"
      "    #100 clk = 1;\n"
      "    #30 d = 1;\n"
      "  end\n"
      "endmodule\n");
}

TEST(NegativeTimingCheckRun, PositiveSetupholdLimitsLeaveTheCopiesUndelayed) {
  EXPECT_EQ(
      DelayedCopyTimes("$setuphold(posedge clk, d, 10, 20, , , , dclk, dd);"),
      "dclk 100\ndd 130\n");
}

TEST(NegativeTimingCheckRun, PositiveRecremLimitsLeaveTheCopiesUndelayed) {
  EXPECT_EQ(DelayedCopyTimes(
                "$recrem(posedge clk, posedge d, 10, 20, , , , dclk, dd);"),
            "dclk 100\ndd 130\n");
}

std::string SkewBesideADelayedClock(const std::string& check) {
  return RunWithTheOption(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d = 0,\n"
      "           output reg e = 0);\n"
      "  reg n = 0;\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, -10, 20);\n"
      "    " +
      check +
      "\n"
      "  endspecify\n"
      "  always @(n) $display(\"%0d\", $time);\n"
      "  initial begin\n"
      "    #100 clk = 1;\n"
      "    #5 e = 1;\n"
      "  end\n"
      "endmodule\n");
}

TEST(NegativeTimingCheckRun, TimeskewKeepsTheUndelayedSignals) {
  EXPECT_EQ(SkewBesideADelayedClock("$timeskew(posedge clk, posedge e, 3, n);"),
            "103\n");
}

TEST(NegativeTimingCheckRun, FullskewKeepsTheUndelayedSignals) {
  EXPECT_EQ(SkewBesideADelayedClock(
                "$fullskew(posedge clk, posedge e, 3, 3, n, 1, 0);"),
            "105\n");
}

std::string SharedClockToggles(const std::string& checks, int d1_at,
                               int d2_at) {
  return RunWithTheOption(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d1 = 0, output reg d2 = 0);\n"
      "  reg n1 = 0, n2 = 0; integer c1 = 0, c2 = 0;\n"
      "  specify\n" +
      checks +
      "  endspecify\n"
      "  always @(n1) c1 = c1 + 1;\n"
      "  always @(n2) c2 = c2 + 1;\n"
      "  initial begin\n"
      "    fork #100 clk = 1; #" +
      std::to_string(d1_at) + " d1 = 1; #" + std::to_string(d2_at) +
      " d2 = 1; join\n"
      "    #50 $display(\"%0d %0d\", c1, c2);\n"
      "  end\n"
      "endmodule\n");
}

constexpr const char* kTwoChecksOnOneClock =
    "    $setuphold(posedge clk, d1, -10, 20, n1);\n"
    "    $setuphold(posedge clk, d2, -15, 18, n2);\n";

TEST(NegativeTimingCheckRun, OneDelayedClockServesBothChecksInTheirWindows) {
  EXPECT_EQ(SharedClockToggles(kTwoChecksOnOneClock, 112, 116), "1 1\n");
  EXPECT_EQ(SharedClockToggles(kTwoChecksOnOneClock, 122, 112), "0 0\n");
  EXPECT_EQ(SharedClockToggles(kTwoChecksOnOneClock, 108, 119), "0 0\n");
}

std::string DelayedClockTime(const std::string& checks) {
  return RunWithTheOption(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d1 = 0, output reg d2 = 0);\n"
      "  specify\n" +
      checks +
      "  endspecify\n"
      "  always @(posedge dclk) $display(\"%0d\", $time);\n"
      "  initial #100 clk = 1;\n"
      "endmodule\n");
}

TEST(NegativeTimingCheckRun, NamedDelayedClockCarriesTheJointDelay) {
  EXPECT_EQ(DelayedClockTime(
                "    $setuphold(posedge clk, d1, -10, 20, , , , dclk, dd1);\n"
                "    $setuphold(posedge clk, d2, -15, 18);\n"),
            "116\n");
}

TEST(NegativeTimingCheckRun, DelayedClockNamedInALaterCheckServesTheFirst) {
  EXPECT_EQ(DelayedClockTime(
                "    $setuphold(posedge clk, d1, -15, 18);\n"
                "    $setuphold(posedge clk, d2, -10, 20, , , , dclk, dd2);\n"),
            "116\n");
  EXPECT_EQ(
      SharedClockToggles(
          "    $setuphold(posedge clk, d1, -15, 18, n1);\n"
          "    $setuphold(posedge clk, d2, -10, 20, n2, , , dclk, dd2);\n",
          116, 112),
      "1 1\n");
}

std::string PathDelayedOutputTime(const std::string& timescale,
                                  const std::string& checks,
                                  const std::string& model) {
  return RunWithTheOption(
      "`timescale " + timescale +
      "\n"
      "module dff(input CLK, input D, output reg Q);\n"
      "  initial Q = 0;\n" +
      model +
      "  specify\n"
      "    (CLK => Q) = 6;\n" +
      checks +
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  reg clk = 0, d = 0; wire q;\n"
      "  dff u(clk, d, q);\n"
      "  always @(posedge q) $display(\"%0.1f\", $realtime);\n"
      "  initial begin\n"
      "    #10 d = 1;\n"
      "    #10 clk = 1;\n"
      "  end\n"
      "endmodule\n");
}

constexpr const char* kLatchThroughTheDelayedClock =
    "  always @(posedge dCLK) Q <= dD;\n";

TEST(NegativeTimingCheckRun, OutputWaitsForAClockDelayedPastThePathDelay) {
  EXPECT_EQ(PathDelayedOutputTime(
                "1ns/100ps",
                "    $setuphold(posedge CLK, posedge D, -3, 8, , , , dCLK, "
                "dD);\n"
                "    $setuphold(posedge CLK, negedge D, -7, 13, , , , dCLK, "
                "dD);\n",
                kLatchThroughTheDelayedClock),
            "27.1\n");
}

TEST(NegativeTimingCheckRun, OutputKeepsItsPathDelayAboveTheClockDelay) {
  EXPECT_EQ(PathDelayedOutputTime(
                "1ns/100ps",
                "    $setuphold(posedge CLK, D, -3, 8, , , , dCLK, dD);\n",
                kLatchThroughTheDelayedClock),
            "26.0\n");
  EXPECT_EQ(PathDelayedOutputTime(
                "1ns/100ps",
                "    $setuphold(posedge CLK, D, -5.9, 8, , , , dCLK, dD);\n",
                kLatchThroughTheDelayedClock),
            "26.0\n");
}

TEST(NegativeTimingCheckRun, OutputWaitsForADataCopyRecremDelays) {
  EXPECT_EQ(PathDelayedOutputTime(
                "1ns/100ps",
                "    $recrem(posedge D, posedge CLK, -3, 8, , , , dD, dCLK);\n"
                "    $recrem(negedge D, posedge CLK, -7, 13, , , , dD, "
                "dCLK);\n",
                "  always @(posedge dCLK) Q <= 1'b1;\n"),
            "27.1\n");
}

std::string DelayedClockRun(const std::string& check,
                            const std::string& stimulus, SimFixture& f) {
  return RunWithTheOption(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d = 0,\n"
      "           output reg e = 0);\n"
      "  reg n = 0;\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, -10, 20);\n"
      "    " +
          check +
          "\n"
          "  endspecify\n"
          "  always @(n) $display(\"%0d\", $time);\n"
          "  initial begin\n"
          "    " +
          stimulus +
          "\n"
          "  end\n"
          "endmodule\n",
      f);
}

std::string DelayedClockRun(const std::string& check,
                            const std::string& stimulus) {
  SimFixture f;
  return DelayedClockRun(check, stimulus, f);
}

TEST(NegativeTimingCheckRun, RecoveryAdjustedToZeroWarnsAndReportsNothing) {
  SimFixture f;
  EXPECT_EQ(DelayedClockRun("$recovery(posedge clk, e, 5, n);",
                            "#100 clk = 1; #2 e = 1;", f),
            "");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "is no longer positive and is set to 0", 7,
                              "31.9.1"));
}

TEST(NegativeTimingCheckRun, RemovalAdjustedToZeroWarnsAndReportsNothing) {
  SimFixture f;
  EXPECT_EQ(DelayedClockRun("$removal(posedge e, clk, 5, n);",
                            "#100 clk = 1; #2 e = 1;", f),
            "");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "is no longer positive and is set to 0", 7,
                              "31.9.1"));
}

TEST(NegativeTimingCheckRun,
     DISABLED_NochangeOffsetAdjustedBelowZeroIsZeroedWithAWarning) {
  SimFixture f;
  EXPECT_EQ(DelayedClockRun("$nochange(posedge clk, e, 0, 4, n);",
                            "#100 clk = 1; #20 clk = 0; #8 e = 1;", f),
            "128\n");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "is no longer positive and is set to 0", 7,
                              "31.9.1"));
}

TEST(NegativeTimingCheckRun, HoldOnADelayedClockUsesItsAdjustedLimit) {
  EXPECT_EQ(DelayedClockRun("$hold(posedge clk, e, 20, n);",
                            "#100 clk = 1; #5 e = 1;"),
            "");
  EXPECT_EQ(DelayedClockRun("$hold(posedge clk, e, 20, n);",
                            "#100 clk = 1; #18 e = 1;"),
            "118\n");
  EXPECT_EQ(DelayedClockRun("$hold(posedge clk, e, 20, n);",
                            "#100 clk = 1; #25 e = 1;"),
            "");
}

TEST(NegativeTimingCheckRun, RecoveryOnADelayedClockUsesItsAdjustedLimit) {
  EXPECT_EQ(DelayedClockRun("$recovery(posedge clk, e, 20, n);",
                            "#100 clk = 1; #5 e = 1;"),
            "");
  EXPECT_EQ(DelayedClockRun("$recovery(posedge clk, e, 20, n);",
                            "#100 clk = 1; #18 e = 1;"),
            "118\n");
  EXPECT_EQ(DelayedClockRun("$recovery(posedge clk, e, 20, n);",
                            "#100 clk = 1; #25 e = 1;"),
            "");
}

TEST(NegativeTimingCheckRun, RemovalOnADelayedClockReportsAtTheDelayedEdge) {
  EXPECT_EQ(DelayedClockRun("$removal(posedge clk, e, 5, n);",
                            "#97 e = 1; #3 clk = 1;"),
            "111\n");
}

TEST(NegativeTimingCheckRun, PositiveSetupholdOnADelayedClockReportsLate) {
  EXPECT_EQ(DelayedClockRun("$setuphold(posedge clk, e, 5, 20, n);",
                            "#97 e = 1; #3 clk = 1;"),
            "111\n");
}

TEST(NegativeTimingCheckRun, SecondRecremOnADelayedClockReportsLate) {
  EXPECT_EQ(DelayedClockRun("$recrem(posedge clk, e, 20, 5, n);",
                            "#97 e = 1; #3 clk = 1;"),
            "111\n");
}

TEST(NegativeTimingCheckRun, PeriodOnADelayedClockReportsAtTheDelayedEdge) {
  EXPECT_EQ(DelayedClockRun("$period(posedge clk, 20, n);",
                            "#100 clk = 1; #5 clk = 0; #5 clk = 1;"),
            "121\n");
}

std::string CopyTimes(const std::string& timescale, const std::string& checks,
                      SimFixture& f) {
  return RunWithTheOption(
      "`timescale " + timescale +
          "\n"
          "module top(output reg a = 0, output reg b = 0);\n"
          "  specify\n" +
          checks +
          "  endspecify\n"
          "  always @(posedge da) $display(\"da %0.2f\", $realtime);\n"
          "  always @(posedge db) $display(\"db %0.2f\", $realtime);\n"
          "  initial #10 begin a = 1; b = 1; end\n"
          "endmodule\n",
      f);
}

std::size_t WarningsSaying(const SimFixture& f, const std::string& text) {
  std::size_t count = 0;
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.message.find(text) != std::string::npos) ++count;
  }
  return count;
}

TEST(NegativeTimingCheckRun, EachRoundOfZeroingWarnsUntilASolution) {
  SimFixture f;
  EXPECT_EQ(CopyTimes("1ns/1ns",
                      "    $setuphold(posedge a, b, -10, 20, , , , da, db);\n"
                      "    $setuphold(posedge b, a, -8, 30);\n"
                      "    $setuphold(posedge b, a, -9, 30);\n",
                      f),
            "db 10.00\nda 21.00\n");
  EXPECT_EQ(WarningsSaying(f, "no consistent delays"), 2u);
}

TEST(NegativeTimingCheckRun, InconsistentRecremLimitsZeroTheLeastNegative) {
  SimFixture f;
  EXPECT_EQ(
      CopyTimes("1ns/1ns",
                "    $recrem(posedge a, posedge b, -10, 20, , , , da, db);\n"
                "    $recrem(posedge b, posedge a, -8, 30);\n",
                f),
      "da 10.00\ndb 21.00\n");
  EXPECT_EQ(WarningsSaying(f, "no consistent delays"), 1u);
}

TEST(NegativeTimingCheckRun, InconsistentMixedLimitsZeroTheLeastNegative) {
  SimFixture f;
  EXPECT_EQ(CopyTimes("1ns/1ns",
                      "    $setuphold(posedge a, b, -10, 20, , , , da, db);\n"
                      "    $recrem(posedge a, posedge b, -8, 30);\n",
                      f),
            "db 10.00\nda 21.00\n");
  EXPECT_EQ(WarningsSaying(f, "no consistent delays"), 1u);
}

TEST(NegativeTimingCheckRun, NegativeRecoveryDelaysTheDataCopy) {
  SimFixture f;
  EXPECT_EQ(
      CopyTimes("1ns/10ps",
                "    $recrem(posedge a, posedge b, -10, 20, , , , da, db);\n",
                f),
      "da 10.00\ndb 20.01\n");
}

TEST(NegativeTimingCheckRun, NegativeRemovalDelaysTheReferenceCopy) {
  SimFixture f;
  EXPECT_EQ(
      CopyTimes("1ns/10ps",
                "    $recrem(posedge a, posedge b, 20, -10, , , , da, db);\n",
                f),
      "db 10.00\nda 20.01\n");
}

std::set<std::string> NamedObjectsWith(const std::string& check) {
  SimFixture f;
  RunWithTheOption(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d = 0);\n"
      "  specify\n"
      "    " +
          check +
          "\n"
          "  endspecify\n"
          "  initial begin #100 clk = 1; #12 d = 1; end\n"
          "endmodule\n",
      f);
  std::set<std::string> names;
  for (const auto& [name, var] : f.ctx.GetVariables()) names.emplace(name);
  for (const auto& [name, net] : f.ctx.GetNets()) names.emplace(name);
  return names;
}

TEST(NegativeTimingCheckRun, ImplicitDelayedCopiesAddNoNamedObject) {
  EXPECT_EQ(NamedObjectsWith("$setuphold(posedge clk, d, -10, 20);"),
            NamedObjectsWith("$setuphold(posedge clk, d, 10, 20);"));
  EXPECT_EQ(NamedObjectsWith("$recrem(posedge clk, posedge d, -10, 20);"),
            NamedObjectsWith("$recrem(posedge clk, posedge d, 10, 20);"));
}

TEST(NegativeTimingCheckRun, ModelOnTheOriginalClockLatchesTheOldData) {
  EXPECT_EQ(
      RunWithTheOption("`timescale 1ns/1ns\n"
                       "module top(output reg q = 0, output reg clk = 0,\n"
                       "           output reg d = 0);\n"
                       "  reg n = 0;\n"
                       "  specify\n"
                       "    $setuphold(posedge clk, d, -10, 20, n);\n"
                       "  endspecify\n"
                       "  always @(posedge clk) #7 q <= d;\n"
                       "  always @(n) $display(\"n %0d\", $time);\n"
                       "  initial begin\n"
                       "    #100 clk = 1; #5 d = 1;\n"
                       "    #50 $display(\"q %b\", q);\n"
                       "  end\n"
                       "endmodule\n"),
      "q 1\n");
}

TEST(NegativeTimingCheckRun, RecremWithoutNamedCopiesUsesImplicitOnes) {
  EXPECT_EQ(TogglesForDataAt("$recrem(posedge r, posedge d, -5, 10, n);",
                             {-12, -7, -3}),
            "0\n1\n0\n");
  EXPECT_EQ(
      TogglesForDataAt("$recrem(posedge r, posedge d, 10, -5, n);", {3, 7, 12}),
      "0\n1\n0\n");
}

}  // namespace
