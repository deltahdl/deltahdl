#include <gtest/gtest.h>

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
      "  initial $display(\"%0d\", $timeprecision($root));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-15\n");
}

TEST(TimescaleSystemFunctions, RootArgumentCountsAPackagesPrecision) {
  SimFixture f;
  std::string out = RunCapture(
      "package p;\n"
      "  timeunit 1ns; timeprecision 10fs;\n"
      "endpackage\n"
      "module top;\n"
      "  timeunit 1ns; timeprecision 1ps;\n"
      "  initial $display(\"%0d\", $timeprecision($root));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-14\n");
}

TEST(TimescaleSystemFunctions, RootArgumentCountsATrailingTimescalePrecision) {
  SimFixture f;
  std::string out = PreprocessAndCapture(
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  initial begin\n"
      "    $display(\"%0d\", $timeprecision($root));\n"
      "    $printtimescale($root);\n"
      "  end\n"
      "endmodule\n"
      "`timescale 1ns / 10ps\n",
      f);
  EXPECT_EQ(out, "-11\nTime scale of ($root) is 10ps / 10ps\n");
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

}  // namespace
