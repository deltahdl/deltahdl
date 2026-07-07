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
#include <iostream>
#include <sstream>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs source through elaboration and simulation, capturing everything written
// to stdout so a $display of the retrieved order can be inspected.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

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

}  // namespace
