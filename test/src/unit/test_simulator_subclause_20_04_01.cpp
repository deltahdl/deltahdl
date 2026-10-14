// §20.4.1 Timescale retrieval system functions. $timeunit and $timeprecision
// return the time unit and precision of a design element, encoded as the
// Table 20-2 base-10 order (an integer in the range 2 to -15). The value each
// function reports depends on which design element it names — the current
// scope with no argument, a named element, the compilation unit ($unit), or
// the simulation time unit ($root, see §3.14.3) — and on how that element's
// timescale was produced by its `timeunit`/`timeprecision` declarations. These
// tests therefore build the timescale from real source and drive it through the
// full pipeline (parse -> elaborate -> lower -> run), reading the returned
// order back through $display so the production selection and Table 20-2
// encoding are observed end to end rather than from a hand-seeded context.
#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

// With no argument, $timeunit reports the current scope's time unit and
// $timeprecision its precision — here the top module's own `timeunit 1ms/1us`
// declaration, encoded as -3 and -6 per Table 20-2.
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

// An argument that names a design element reports that element's timescale. The
// top module names itself; its declared 100us/10ns maps to -4 and -8.
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

// A named argument resolves the *named* child instance, not the calling scope:
// the parent runs at 1ns/1ns while the instance c1 declares 100ps/10fs, so
// $timeunit(c1)/$timeprecision(c1) report the child's -10 and -14.
TEST(TimescaleSystemFunctions, NamedInstanceArgumentReportsChildTimescale) {
  SimFixture f;
  std::string out = RunCapture(
      "module child;\n"
      "  timeunit 100ps / 10fs;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  initial begin\n"
      "    if ($timeunit(c1) == -10) $display(\"unit_ok\");\n"
      "    if ($timeprecision(c1) == -14) $display(\"prec_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "unit_ok\nprec_ok\n");
}

// The $unit argument reports the compilation unit's timescale, set here by a
// compilation-unit-scope `timeunit 1s/1ms` declaration (order 0 and -3).
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

// The $root argument yields the simulation time unit for both functions — the
// smallest precision across the design (§3.14.3). With the module declaring a
// 1ps precision, both report -12.
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

// A magnitude of 10 or 100 shifts the Table 20-2 order up by one or two. Here
// 10s -> 1 for the unit and 100ns -> -7 for the precision, exercising the
// off-decade rows the plain 1-magnitude cases never reach.
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

// With no timescale declared anywhere the current scope defaults to 1ns, so
// both functions report -9.
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

// The returned order stays within the Table 20-2 range of 2 to -15: the
// coarsest unit (100s -> 2) and the finest precision (1fs -> -15) sit at the
// two extremes.
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

// §20.4.1 with §3.14.3: the simulation time unit is the smallest time
// precision in the design, magnitude and all, so a design whose finest
// precision is 100 ps answers -10 for $root, from two modules whose precisions
// are 100 ps and 1 ns; and $printtimescale($root) names it for both fields.
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

// §20.4.1, §20.4.2: an instance named as the argument answers that element's
// unit and precision, and the process goes on to the statements after the
// call: $timeunit(s1) and $timeprecision(s1) are the instance's -9 and -12,
// $printtimescale(s1) reports it, and the display after them runs.
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

// §20.4.1 with §3.14.3: the global time precision counts the compilation
// unit's precision as well as the instances', so the 1fs the unit declares,
// finer than top's 1ps, is what $root answers.
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

// §20.4.1 with §3.14.3: a package's precision counts toward the global one,
// magnitude and all, though no instance holds it: the 10fs of p makes $root
// answer -14, where top alone gives -12 and the unit without its magnitude
// -15.
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

// §20.4.1 and §20.4.2 with §3.14.3: every `timescale precision counts toward
// the global one, magnitude and all, a directive that stands before no design
// element's header included: the trailing 1ns / 10ps makes $root's precision
// 10ps, where top alone gives 1ns and the unit without its magnitude 1ps.
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

// §20.4.1 and §20.4.2: an argument may name an instance through the
// instances above it, as the standard's own b_dat.c1 does. a_dat's 1ms / 1us
// is what a dotted name that resolved to nothing would report in place of
// c1's 1ns / 1ns.
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

// §20.4.1 and §20.4.2 with §3.2: a package is a design element, so naming one
// reports the time scale it declares rather than the calling module's.
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
