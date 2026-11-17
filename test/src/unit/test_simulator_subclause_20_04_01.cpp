#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

TEST(TimescaleSystemFunctions, NoArgumentReportsCurrentScopeUnitAndPrecision) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ms / 1us;\n"
      "  initial begin\n"
      "    if ($timeunit == -3) $display(\"unit_ok\");\n"
      "    if ($timeprecision == -6) $display(\"prec_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "unit_ok\nprec_ok\n");
}

TEST(TimescaleSystemFunctions, NamedElementArgumentReportsThatElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module dut;\n"
      "  timeunit 100us / 10ns;\n"
      "  initial begin\n"
      "    if ($timeunit(dut) == -4) $display(\"unit_ok\");\n"
      "    if ($timeprecision(dut) == -8) $display(\"prec_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "unit_ok\nprec_ok\n");
}

TEST(TimescaleSystemFunctions, NamedInstanceArgumentReportsChildTimescale) {
  SimFixture f;
  std::string out = RunCapture(
      "module child;\n"
      "  timeunit 100ps / 10fs;\n"
      "endmodule\n"
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  child c1();\n"
      "  initial begin\n"
      "    if ($timeunit(c1) == -10) $display(\"unit_ok\");\n"
      "    if ($timeprecision(c1) == -14) $display(\"prec_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "unit_ok\nprec_ok\n");
}

TEST(TimescaleSystemFunctions, UnitArgumentReportsCompilationUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "timeunit 1s / 1ms;\n"
      "module top;\n"
      "  initial begin\n"
      "    if ($timeunit($unit) == 0) $display(\"unit_ok\");\n"
      "    if ($timeprecision($unit) == -3) $display(\"prec_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "unit_ok\nprec_ok\n");
}

TEST(TimescaleSystemFunctions, RootArgumentReportsSimulationTimeUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  timeunit 1ns / 1ps;\n"
      "  initial begin\n"
      "    if ($timeunit($root) == -12) $display(\"unit_ok\");\n"
      "    if ($timeprecision($root) == -12) $display(\"prec_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "unit_ok\nprec_ok\n");
}

TEST(TimescaleSystemFunctions, MagnitudeMultiplierShiftsTableOrder) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10s / 100ns;\n"
      "  initial begin\n"
      "    if ($timeunit == 1) $display(\"unit_ok\");\n"
      "    if ($timeprecision == -7) $display(\"prec_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "unit_ok\nprec_ok\n");
}

TEST(TimescaleSystemFunctions, DefaultCurrentScopeIsNanosecond) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    if ($timeunit == -9) $display(\"unit_ok\");\n"
      "    if ($timeprecision == -9) $display(\"prec_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "unit_ok\nprec_ok\n");
}

TEST(TimescaleSystemFunctions, ReturnValueSpansTableRange) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 100s / 1fs;\n"
      "  initial begin\n"
      "    if ($timeunit == 2) $display(\"unit_ok\");\n"
      "    if ($timeprecision == -15) $display(\"prec_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "unit_ok\nprec_ok\n");
}

TEST(TimescaleSystemFunctions, RootArgumentKeepsThePrecisionsMagnitude) {
  SimFixture f;
  std::string out = RunCapture(
      "module leaf;\n"
      "  timeunit 10ns / 100ps;\n"
      "endmodule\n"
      "module top;\n"
      "  timeunit 1us / 1ns;\n"
      "  leaf l();\n"
      "  initial begin\n"
      "    $display(\"%0d %0d\", $timeunit($root), $timeprecision($root));\n"
      "    $printtimescale($root);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-10 -10\nTime scale of ($root) is 100ps / 100ps\n");
}

TEST(TimescaleSystemFunctions, AnInstanceArgumentReportsItAndTheProcessGoesOn) {
  SimFixture f;
  std::string out = RunCapture(
      "module s;\n"
      "  timeunit 1ns / 1ps;\n"
      "endmodule\n"
      "module t;\n"
      "  timeunit 10ns / 100ps;\n"
      "  s s1();\n"
      "  initial begin\n"
      "    $display(\"%0d %0d\", $timeunit(s1), $timeprecision(s1));\n"
      "    $printtimescale(s1);\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-9 -12\nTime scale of (s1) is 1ns / 1ps\ndone\n");
}

TEST(TimescaleSystemFunctions, RootArgumentCountsTheCompilationUnitsPrecision) {
  SimFixture f;
  std::string out = RunCapture(
      "timeunit 1ns;\n"
      "timeprecision 1fs;\n"
      "module top;\n"
      "  timeunit 1ns; timeprecision 1ps;\n"
      "  initial $display(\"%0d %0d\", $timeunit($root), "
      "$timeprecision($root));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-15 -15\n");
}

TEST(TimescaleSystemFunctions, RootArgumentCountsAPackagesPrecision) {
  SimFixture f;
  std::string out = RunCapture(
      "package p;\n"
      "  timeunit 1ns; timeprecision 10fs;\n"
      "endpackage\n"
      "module top;\n"
      "  timeunit 1ns; timeprecision 1ps;\n"
      "  initial $display(\"%0d %0d\", $timeunit($root), "
      "$timeprecision($root));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-14 -14\n");
}

TEST(TimescaleSystemFunctions, RootArgumentCountsATrailingTimescalePrecision) {
  SimFixture f;
  std::string out = PreprocessAndCapture(
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  initial begin\n"
      "    $display(\"%0d %0d\", $timeunit($root), $timeprecision($root));\n"
      "    $printtimescale($root);\n"
      "  end\n"
      "endmodule\n"
      "`timescale 1ns / 10ps\n",
      f);
  EXPECT_EQ(out, "-11 -11\nTime scale of ($root) is 10ps / 10ps\n");
}

TEST(TimescaleSystemFunctions, AHierarchicalArgumentReportsTheInstanceItNames) {
  SimFixture f;
  std::string out = PreprocessAndCapture(
      "`timescale 1 ns / 1 ns\n"
      "module c_dat;\n"
      "endmodule\n"
      "`timescale 10 fs / 1 fs\n"
      "module b_dat;\n"
      "  c_dat c1 ();\n"
      "endmodule\n"
      "module a_dat;\n"
      "  timeunit 1ms / 1us;\n"
      "  b_dat b ();\n"
      "  initial begin\n"
      "    $display(\"%0d %0d\", $timeunit(b.c1), $timeprecision(b.c1));\n"
      "    $printtimescale(b.c1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-9 -9\nTime scale of (b.c1) is 1ns / 1ns\n");
}

TEST(TimescaleSystemFunctions, APackageArgumentReportsThePackage) {
  SimFixture f;
  std::string out = RunCapture(
      "package p;\n"
      "  timeunit 1us / 1ns;\n"
      "endpackage\n"
      "module top;\n"
      "  timeunit 1ns / 1ps;\n"
      "  initial begin\n"
      "    $display(\"%0d %0d\", $timeunit(p), $timeprecision(p));\n"
      "    $printtimescale(p);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-6 -9\nTime scale of (p) is 1us / 1ns\n");
}

std::string RunSource(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(TimescaleSystemFunctions, EveryTableRowNotYetShownReturnsItsOrder) {
  EXPECT_EQ(
      RunSource(
          "module m2;\n"
          "  timeunit 10us / 100fs;\n"
          "  initial #1 $display(\"%0d %0d\", $timeunit, $timeprecision);\n"
          "endmodule\n"
          "module m1;\n"
          "  timeunit 100ms / 10ms;\n"
          "  m2 u();\n"
          "  initial $display(\"%0d %0d\", $timeunit, $timeprecision);\n"
          "endmodule\n"),
      "-1 -2\n-5 -13\n");
}

TEST(TimescaleSystemFunctions, TheResultIsAThirtyTwoBitInteger) {
  EXPECT_EQ(RunSource("module t;\n"
                      "  timeunit 1ns / 1ps;\n"
                      "  initial $display(\"%0d %0d %0d\", $bits($timeunit),\n"
                      "    $bits($timeprecision), $timeprecision < 0);\n"
                      "endmodule\n"),
            "32 32 1\n");
}

TEST(TimescaleSystemFunctions, ANestedModuleReadsItsInheritedScale) {
  EXPECT_EQ(
      RunSource(
          "module top;\n"
          "  timeunit 1us;\n"
          "  timeprecision 10ps;\n"
          "  module inner;\n"
          "    initial $display(\"%0d %0d\", $timeunit, $timeprecision);\n"
          "  endmodule\n"
          "  inner u();\n"
          "endmodule\n"),
      "-6 -11\n");
}

TEST(TimescaleSystemFunctions, AnInterfaceReadsItsOwnScale) {
  EXPECT_EQ(
      RunSource("interface i;\n"
                "  timeunit 10us;\n"
                "  timeprecision 1ns;\n"
                "  initial $display(\"%0d %0d\", $timeunit, $timeprecision);\n"
                "endinterface\n"
                "module top;\n"
                "  timeunit 1ns / 1ps;\n"
                "  i u();\n"
                "endmodule\n"),
      "-5 -9\n");
}

TEST(TimescaleSystemFunctions, AProgramReadsItsOwnScale) {
  EXPECT_EQ(
      RunSource("program p;\n"
                "  timeunit 100ms;\n"
                "  timeprecision 10us;\n"
                "  initial $display(\"%0d %0d\", $timeunit, $timeprecision);\n"
                "endprogram\n"
                "module top;\n"
                "  timeunit 1ns / 1ps;\n"
                "  p u();\n"
                "endmodule\n"),
      "-1 -5\n");
}

TEST(TimescaleSystemFunctions, APackageSubroutineReadsThePackagesScale) {
  EXPECT_EQ(RunSource("package pk;\n"
                      "  timeunit 10ms;\n"
                      "  timeprecision 100fs;\n"
                      "  function void show();\n"
                      "    $display(\"%0d %0d\", $timeunit, $timeprecision);\n"
                      "  endfunction\n"
                      "  task run();\n"
                      "    $display(\"%0d %0d\", $timeunit, $timeprecision);\n"
                      "  endtask\n"
                      "endpackage\n"
                      "module top;\n"
                      "  timeunit 1ns / 1ps;\n"
                      "  initial begin\n"
                      "    pk::show();\n"
                      "    pk::run();\n"
                      "  end\n"
                      "endmodule\n"),
            "-2 -13\n-2 -13\n");
}

TEST(TimescaleSystemFunctions, AFunctionCalledHierarchicallyReadsItsModule) {
  EXPECT_EQ(RunSource("module a;\n"
                      "  timeunit 1us;\n"
                      "  timeprecision 1ns;\n"
                      "  function void f();\n"
                      "    $display(\"%0d %0d\", $timeunit, $timeprecision);\n"
                      "  endfunction\n"
                      "endmodule\n"
                      "module top;\n"
                      "  timeunit 1ns;\n"
                      "  timeprecision 1ps;\n"
                      "  a ia();\n"
                      "  initial ia.f();\n"
                      "endmodule\n"),
            "-6 -9\n");
}

TEST(TimescaleSystemFunctions, AnInterfaceOrProgramInstanceArgumentNamesIt) {
  EXPECT_EQ(
      RunSource("interface i;\n"
                "  timeunit 10us;\n"
                "  timeprecision 1ns;\n"
                "endinterface\n"
                "program p;\n"
                "  timeunit 100ms;\n"
                "  timeprecision 10us;\n"
                "endprogram\n"
                "module top;\n"
                "  timeunit 1ns / 1ps;\n"
                "  i ui();\n"
                "  p up();\n"
                "  initial $display(\"%0d %0d %0d %0d\", $timeunit(ui),\n"
                "    $timeprecision(ui), $timeunit(up), $timeprecision(up));\n"
                "endmodule\n"),
      "-5 -9 -1 -5\n");
}

TEST(TimescaleSystemFunctions, TheStandardsExampleRetrievesEveryScale) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCaptureAllTops(
                "timeunit 100ps / 10fs;\n"
                "module a_dat;\n"
                "  timeunit 1ms / 1us;\n"
                "  initial begin\n"
                "    $display(\"Simulation time unit: %0d, precision: %0d\",\n"
                "      $timeunit($root), $timeprecision($root));\n"
                "    $display(\"Compilation time unit: %0d, precision: %0d\",\n"
                "      $timeunit($unit), $timeprecision($unit));\n"
                "    $display(\"a_dat time unit: %0d, precision: %0d\",\n"
                "      $timeunit, $timeprecision);\n"
                "    $display(\"b_dat.c1 time unit: %0d, precision: %0d\",\n"
                "      $timeunit(b_dat.c1), $timeprecision(b_dat.c1));\n"
                "  end\n"
                "endmodule\n"
                "`timescale 10 fs / 1 fs\n"
                "module b_dat;\n"
                "  c_dat c1 ();\n"
                "endmodule\n"
                "`timescale 1 ns / 1 ns\n"
                "module c_dat;\n"
                "endmodule\n",
                f),
            "Simulation time unit: -15, precision: -15\n"
            "Compilation time unit: -10, precision: -14\n"
            "a_dat time unit: -3, precision: -6\n"
            "b_dat.c1 time unit: -9, precision: -9\n");
}

}  // namespace
