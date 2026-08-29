// Whether a running design's $width check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Both cases here write a design, drive its one signal from an initial block,
// and read back the diagnostics standing on the fixture. Neither builds a
// TimingCheckEntry, and neither calls SpecifyManager::CheckWidthViolation. That
// is what separates this file from test_simulator_subclause_31_04_04a.cpp
// beside it: every case there hands the predicate a reference time, a data time
// and a limit and asks for the verdict, so each proves the verdict is right
// once something asks and none proves that anything asks. Issue #3409 is that
// nothing did -- every caller of that predicate in the tree was a unit test, so
// no §31.4.4 violation was ever reported out of a run.
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
// when the design gains or loses a line above the $width.
//
// §31.4.4 bounds its window with two edges of ONE signal, which no other driven
// case reaches. Table 31-10 makes the data event implicit -- "the data event
// and the reference event ... are triggered by opposite transitions" -- so a
// posedge reference makes the following negedge the timecheck, and the check
// reports when
//
//   threshold < (timecheck time) - (timestamp time) < limit
//
// §31.3's stability windows and §31.4.1 through §31.4.3's skew checks all
// measure between two named signals, so a driver written for either shape does
// not reach this one.
//
// The two cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to both: a
// driver that reported unconditionally would fail the satisfied case, and a
// driver that reported nothing would fail the violating one.
//
// The threshold is written as 0, which is the value §31.4.4 gives it when it is
// left out, and no case here turns on it. Issue #3418 is why: a declared
// threshold never reaches the registered check, because
// BuildTimingCheckUnderOptions in src/simulator/specify_timing_check.cpp never
// assigns TimingCheckEntry::threshold and Parser::ParseTimingCheckTrailingArgs
// puts the threshold into the same limits list as the limit, whence it is
// written to TimingCheckEntry::limit2 and read by nothing. A case whose
// expected answer depended on a non-zero declared threshold would fail on that
// defect rather than on §31.4.4, so §31.4.4's glitch rule -- "no violation is
// reported for glitches smaller than the threshold" -- is left uncovered here.
//
// The message substring stops before the signal name the report goes on to
// spell. What the violating case claims is that the violation was found and
// named as §31.4.4's, and naming a signal in the substring would tie it to
// which field it reached the report through as well.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.4.3, §31.4.5
// and §31.4.6 beside this one. The limit is 5, not the 0 a
// TimingCheckEntry::limit holds before a limit expression has been evaluated
// into it. The violating case holds the pulse for 3 time units and the
// satisfied case for 7, one below the limit and one above, and the pulses open
// at times 806 and 840, so a case that read its interval, its limit or its edge
// out of another case's design would compare two numbers that disagree rather
// than two that coincide.
//
// Each source drives the signal to a known level before the pulse that matters.
// §31.5 makes posedge the shorthand for edge[01, 0x, x1], so the x-to-0
// assignment at time 0 is no posedge and opens no window; the negedge it does
// answer to closes no window, there being no timestamp before it.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.
//
// Syntax 31-12 writes `$width(controlled_reference_event, timing_check_limit,
// threshold, notifier)` and names one signal only, the reference event, which
// §31.4.4 requires be an edge specification.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The design every case here runs, up to the point the stimulus is spliced in.
// It is a named constant rather than a literal inside the call below so that a
// case can name the line its $width stands on with LineHolding
// (lib/cpp/test_helpers/helpers_reported_error.h). The stimulus follows the
// check, so a line of this text is that line of the whole source.
constexpr const char* kDesignBeforeStimulus =
    "module top;\n"
    "  logic clk;\n"
    "  specify\n"
    "    $width(posedge clk, 5, 0);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clk = 1'b0;\n";

// Elaborates, lowers and runs the one design these cases share, with `stimulus`
// as the body of its initial block. False when the source did not elaborate
// cleanly, which a case asserts on before reading anything off the fixture: a
// design rejected before it ran says nothing about §31.4.4 whatever the case
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

// §31.4.4: `clk` rises at time 806 and falls at time 809, holding its level for
// 3 time units against a limit of 5.
TEST(DrivenTimingCheckEvaluation, WidthViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #806 clk = 1'b1;\n"
                      "    #3 clk = 1'b0;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$width violation: signal",
      LineHolding(kDesignBeforeStimulus, "$width(posedge clk"), "31.4.4"));
}

// §31.4.4 again, and the same design: only the stimulus changes. `clk` rises at
// time 840 and falls at time 847, holding its level for 7 time units against
// the same limit of 5, which §31.4.4 states as the pulse width being "greater
// than or equal to limit in order to avoid a timing violation".
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $width site can make about any design carries this substring and
// there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, WidthSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #840 clk = 1'b1;\n"
                      "    #7 clk = 1'b0;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$width violation: signal"), nullptr);
}

}  // namespace
