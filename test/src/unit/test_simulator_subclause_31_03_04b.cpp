// Whether a running design's $removal check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Both cases here write a design, drive its two signals from an initial block,
// and read back the diagnostics standing on the fixture. Neither builds a
// TimingCheckEntry, and neither calls
// SpecifyManager::CheckRemovalViolation. That is what separates this file from
// test_simulator_subclause_31_03_04a.cpp beside it: every case there hands the
// predicate a reference time, a data time and a limit and asks for the verdict,
// so each proves the verdict is right once something asks and none proves that
// anything asks. Issue #3409 is that nothing did -- every caller of that
// predicate in the tree was a unit test, so no §31.3.4 violation was ever
// reported out of a run.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportTimingViolation in src/simulator/timing_check_driver_internal.h calls
// DiagEngine::Warning; the cases below read it through ReportedWarning rather
// than ReportedError. It stands at SourceLoc::None(), whose line is 0, because
// TimingCheckEntry records no position for the declaration it was built from.
//
// §31.3.4 makes the reference event the timecheck event and the data event the
// timestamp event -- Table 31-4 -- so the window ENDS at the reference edge:
//
//   (beginning of time window) = (timecheck time) - limit
//   (end of time window)       = (timecheck time)
//
// and the check reports when begin < timestamp time < end, both end points
// excluded. That direction is the opposite of §31.3.5's $recovery, whose window
// begins at the reference edge, so neither file restates the other. Both
// stimuli below stand clear of the end points, so what they assert does not
// turn on the exclusions.
//
// The two cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to both: a
// driver that reported unconditionally would fail the satisfied case, and a
// driver that reported nothing would fail the violating one.
//
// The message substring stops before the signal name the report goes on to
// spell. What the violating case claims is that the violation was found and
// named as §31.3.4's, and naming a signal in the substring would tie it to
// which field each reached the report through as well.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 and §31.3.5 through §31.4.6
// beside this one. The limit is 18, not the 0 a TimingCheckEntry::limit holds
// before a limit expression has been evaluated into it. The violating case
// leaves 8 time units between the transitions and the satisfied case 25, and
// the reference edges stand at times 213 and 265, so a case that read its
// interval, its limit or its edge out of another case's design would compare
// two numbers that disagree rather than two that coincide.
//
// Each source drives both signals to a known level before either transition
// that matters. §31.5 makes posedge the shorthand for edge[01, 0x, x1], so the
// x-to-0 assignments at time 0 are no posedge and the timeline of each case
// begins at the first delay.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.
//
// Syntax 31-6 writes `$removal(reference_event, data_event,
// timing_check_limit, ...)`, the reference event first, and §31.3.4 has that
// reference event usually a control signal like clear, reset or set with the
// data event usually a clock. `rst` and `clk` are named for those roles.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// Elaborates, lowers and runs the one design these cases share, with `stimulus`
// as the body of its initial block. False when the source did not elaborate
// cleanly, which a case asserts on before reading anything off the fixture: a
// design rejected before it ran says nothing about §31.3.4 whatever the case
// was written to expect.
bool RanWithStimulus(const std::string& stimulus, SimFixture& f) {
  auto* rtl =
      ElaborateSrc(std::string("module top;\n"
                               "  logic rst;\n"
                               "  logic clk;\n"
                               "  specify\n"
                               "    $removal(posedge rst, posedge clk, 18);\n"
                               "  endspecify\n"
                               "  initial begin\n"
                               "    rst = 1'b0;\n"
                               "    clk = 1'b0;\n") +
                       stimulus +
                       "  end\n"
                       "endmodule\n",
                   f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

// §31.3.4: `clk` rises at time 205 and `rst` rises at time 213, so the window
// runs from 195 to 213 and the data transition stands 8 time units inside it
// against a limit of 18.
TEST(DrivenTimingCheckEvaluation, RemovalViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #205 clk = 1'b1;\n"
                      "    #8 rst = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$removal violation: data signal", 0, "31.3.4"));
}

// §31.3.4 again, and the same design: only the stimulus changes. `clk` rises at
// time 240 and `rst` rises at time 265, so the window runs from 247 to 265 and
// the data transition at 240 stands before it opens.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $removal site can make about any design carries this substring and
// there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, RemovalSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #240 clk = 1'b1;\n"
                      "    #25 rst = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$removal violation: data signal"), nullptr);
}

}  // namespace
