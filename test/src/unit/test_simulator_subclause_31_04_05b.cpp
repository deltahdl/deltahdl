// Whether a running design's $period check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Both cases here write a design, drive its one signal from an initial block,
// and read back the diagnostics standing on the fixture. Neither builds a
// TimingCheckEntry, and neither calls SpecifyManager::CheckPeriodViolation.
// That is what separates this file from test_simulator_subclause_31_04_05a.cpp
// beside it: every case there hands the predicate a reference time, a data time
// and a limit and asks for the verdict, so each proves the verdict is right
// once something asks and none proves that anything asks. Issue #3409 is that
// nothing did -- every caller of that predicate in the tree was a unit test, so
// no §31.4.5 violation was ever reported out of a run.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportTimingViolation in src/simulator/timing_check_driver_internal.h calls
// DiagEngine::Warning; the cases below read it through ReportedWarning rather
// than ReportedError. It stands on the line the check was written on, which
// TimingCheckEntry::loc in src/simulator/specify_timing_check.h carries from
// Parser::ParseTimingCheck in src/parser/parser_specify.cpp. Issue #3414 is
// that it did not: the report stood at SourceLoc::None(), whose line is 0,
// because nothing carried the check's position from the declaration to the run.
// The violating case below names that line with LineHolding over
// kDesignBeforeStimulus rather than writing a number, so the case cannot drift
// when the design gains or loses a line above the $period.
//
// §31.4.5 names one signal and derives the data event from it -- "data event =
// reference event signal with the same edge" -- so the window runs between
// consecutive matching edges of that signal and the check reports when
//
//   (timecheck time) - (timestamp time) < limit
//
// That is the same edge twice, where §31.4.4's $width takes opposite edges of
// one signal and §31.3's stability windows take one edge of each of two
// signals, so a driver written for either does not reach this rule. The
// intervening negedge each stimulus drives is what lets the second posedge
// happen at all and is no event of this check.
//
// The two cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to both: a
// driver that reported unconditionally would fail the satisfied case, and a
// driver that reported nothing would fail the violating one.
//
// The message substring stops before the signal name the report goes on to
// spell. What the violating case claims is that the violation was found and
// named as §31.4.5's, and naming a signal in the substring would tie it to
// which field it reached the report through as well.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.4.4 and §31.4.6
// beside this one. The limit is 61, not the 0 a TimingCheckEntry::limit holds
// before a limit expression has been evaluated into it. The violating case puts
// 44 time units between its two posedges and the satisfied case 78, one below
// the limit and one above; the pulses within them are 16 and 31 time units
// long, distinct from the periods they sit inside so that a driver measuring
// between opposite edges rather than matching ones compares two numbers that
// disagree; and the first posedges stand at times 902 and 950. So a case that
// read its interval, its limit or its edge out of another case's design would
// compare two numbers that disagree rather than two that coincide.
//
// Each source drives the signal to a known level before the edges that matter.
// §31.5 makes posedge the shorthand for edge[01, 0x, x1], so the x-to-0
// assignment at time 0 is no posedge and is not one of the two edges a case
// counts.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.
//
// Syntax 31-13 writes `$period(controlled_reference_event, timing_check_limit
// [, notifier])` and names one signal only, the reference event, which §31.4.5
// requires be an edge specification.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The design every case here runs, up to the point the stimulus is spliced in.
// It is a named constant rather than a literal inside the call below so that a
// case can name the line its $period stands on with LineHolding
// (lib/cpp/test_helpers/helpers_reported_error.h). The stimulus follows the
// check, so a line of this text is that line of the whole source.
constexpr const char* kDesignBeforeStimulus =
    "module top;\n"
    "  logic clk;\n"
    "  specify\n"
    "    $period(posedge clk, 61);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clk = 1'b0;\n";

// Elaborates, lowers and runs the one design these cases share, with `stimulus`
// as the body of its initial block. False when the source did not elaborate
// cleanly, which a case asserts on before reading anything off the fixture: a
// design rejected before it ran says nothing about §31.4.5 whatever the case
// was written to expect.
bool RanWithStimulus(const std::string& stimulus, SimFixture& f) {
  auto* rtl = ElaborateSrc(std::string(kDesignBeforeStimulus) + stimulus +
                               "  end\n"
                               "endmodule\n",
                           f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

// §31.4.5: `clk` rises at time 902, falls at time 918 and rises again at time
// 946, repeating its edge after 44 time units against a limit of 61.
TEST(DrivenTimingCheckEvaluation, PeriodViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #902 clk = 1'b1;\n"
                      "    #16 clk = 1'b0;\n"
                      "    #28 clk = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$period violation: signal",
      LineHolding(kDesignBeforeStimulus, "$period(posedge clk"), "31.4.5"));
}

// §31.4.5 again, and the same design: only the stimulus changes. `clk` rises at
// time 950, falls at time 981 and rises again at time 1028, repeating its edge
// after 78 time units against the same limit of 61.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $period site can make about any design carries this substring and
// there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, PeriodSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #950 clk = 1'b1;\n"
                      "    #31 clk = 1'b0;\n"
                      "    #47 clk = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$period violation: signal"), nullptr);
}

}  // namespace
