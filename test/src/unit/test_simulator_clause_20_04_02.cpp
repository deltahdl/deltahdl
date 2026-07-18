// §20.4.2 $printtimescale — the system task that displays a design element's
// time unit and precision in the fixed format
// "Time scale of (<name>) is <unit> / <precision>". Which element is reported
// depends on the argument: the current scope with no argument, a named design
// element, the compilation unit ($unit), or the simulation time unit ($root,
// see §3.14.3, whose unit and precision are synonymous). What the task prints
// therefore depends on how each element's timescale was produced by its
// `timeunit` declarations (the §3.14.3 / §20.4.1 machinery this pass depends
// on). These tests build the timescale from real source and drive it through
// the full pipeline (parse -> elaborate -> lower -> run), capturing the line
// $printtimescale writes to stdout, rather than hand-seeding a context.
#include <iostream>
#include <sstream>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single top-module source through elaboration and simulation while
// capturing everything the run writes to stdout, so the line(s) $printtimescale
// emits can be inspected.
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

// §20.4.2: with no argument, $printtimescale describes the design element that
// is the current scope. Here the top module's own `timeunit 1ms / 1us`
// declaration is reported, with the module name standing in for the element.
TEST(PrinttimescaleSysTask, NoArgumentDescribesCurrentScope) {
  SimFixture f;
  std::string out = RunCapture(
      "module a_dat;\n"
      "  timeunit 1ms / 1us;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (a_dat) is 1ms / 1us\n");
}

// §20.4.2: a named argument selects that design element, and its own time unit
// and precision are shown. The parent runs at 1ns while the instantiated child
// c1 declares 100ps / 10fs, so naming c1 reports the child's timescale, not the
// caller's.
TEST(PrinttimescaleSysTask, NamedElementArgumentDescribesThatElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module child;\n"
      "  timeunit 100ps / 10fs;\n"
      "endmodule\n"
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  child c1();\n"
      "  initial $printtimescale(c1);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (c1) is 100ps / 10fs\n");
}

// §20.4.2: the $unit argument describes the compilation unit, and the literal
// "$unit" stands in for the design-element name. The compilation-unit timescale
// is set by a compilation-unit-scope `timeunit 1s / 1ms` declaration.
TEST(PrinttimescaleSysTask, UnitArgumentDescribesCompilationUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "timeunit 1s / 1ms;\n"
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  initial $printtimescale($unit);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of ($unit) is 1s / 1ms\n");
}

// §20.4.2: the $root argument describes the simulation time unit, and the
// literal "$root" stands in for the design-element name. The simulation time
// unit and the global precision are synonymous (§3.14.3), so both fields are
// identical — here the module's 1fs precision makes the finest precision in the
// design 1fs, reported for unit and precision alike.
TEST(PrinttimescaleSysTask, RootArgumentDescribesSimulationTimeUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  timeunit 1ns / 1fs;\n"
      "  initial $printtimescale($root);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of ($root) is 1fs / 1fs\n");
}

// §20.4.2 (shall): the report follows the fixed format
// "Time scale of (<name>) is <unit> / <precision>". An off-decade magnitude
// (100 us for the unit, 10 ns for the precision) exercises the Table 20-2
// rendering of the two fields.
TEST(PrinttimescaleSysTask, ReportFollowsRequiredFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module dut;\n"
      "  timeunit 100us / 10ns;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (dut) is 100us / 10ns\n");
}

// §20.4.2 (shall) edge case: the report renders whole-second units at the top
// of Table 20-2 (orders 2 and 1), exercising the positive-order branch of the
// magnitude-and-unit formatting that the sub-second cases never reach.
TEST(PrinttimescaleSysTask, RendersWholeSecondUnits) {
  SimFixture f;
  std::string out = RunCapture(
      "module slow;\n"
      "  timeunit 100s / 10s;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (slow) is 100s / 10s\n");
}

// §20.4.2 edge case: with no timescale declared anywhere the current scope
// defaults to 1 ns for both unit and precision.
TEST(PrinttimescaleSysTask, DefaultCurrentScopeIsNanosecond) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (top) is 1ns / 1ns\n");
}

}  // namespace
