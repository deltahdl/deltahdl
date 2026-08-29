// Whether a running design's $recovery check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Both cases here write a design, drive its two signals from an initial block,
// and read back the diagnostics standing on the fixture. Neither builds a
// TimingCheckEntry, and neither calls
// SpecifyManager::CheckRecoveryViolation. That is what separates this file from
// test_simulator_subclause_31_03_05a.cpp beside it: every case there hands the
// predicate a reference time, a data time and a limit and asks for the verdict,
// so each proves the verdict is right once something asks and none proves that
// anything asks. Issue #3409 is that nothing did -- every caller of that
// predicate in the tree was a unit test, so no §31.3.5 violation was ever
// reported out of a run.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportTimingViolation in src/simulator/timing_check_driver_internal.h calls
// DiagEngine::Warning; the cases below read it through ReportedWarning rather
// than ReportedError. It stands at SourceLoc::None(), whose line is 0, because
// TimingCheckEntry records no position for the declaration it was built from.
//
// §31.3.5 makes the reference event the timestamp event and the data event the
// timecheck event -- Table 31-5 -- so the window BEGINS at the reference edge:
//
//   (beginning of time window) = (timestamp time)
//   (end of time window)       = (timestamp time) + limit
//
// and the check reports when begin <= timecheck time < end, the beginning
// included and the end excluded. That direction is the opposite of §31.3.4's
// $removal, whose window ends at the reference edge, so neither file restates
// the other. Both stimuli below stand clear of the end points, so what they
// assert does not turn on which end point each rule includes.
//
// The two cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to both: a
// driver that reported unconditionally would fail the satisfied case, and a
// driver that reported nothing would fail the violating one.
//
// The message substring stops before the signal name the report goes on to
// spell. What the violating case claims is that the violation was found and
// named as §31.3.5's, and naming a signal in the substring would tie it to
// which field each reached the report through as well.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3, §31.3.4 and §31.3.6
// through §31.4.6 beside this one. The limit is 22, not the 0 a
// TimingCheckEntry::limit holds before a limit expression has been evaluated
// into it. The violating case leaves 10 time units between the transitions and
// the satisfied case 37, and the reference edges stand at times 302 and 345, so
// a case that read its interval, its limit or its edge out of another case's
// design would compare two numbers that disagree rather than two that coincide.
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
// Syntax 31-7 writes `$recovery(reference_event, data_event,
// timing_check_limit, ...)`, the reference event first, and §31.3.5 has that
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
// design rejected before it ran says nothing about §31.3.5 whatever the case
// was written to expect.
bool RanWithStimulus(const std::string& stimulus, SimFixture& f) {
  auto* rtl =
      ElaborateSrc(std::string("module top;\n"
                               "  logic rst;\n"
                               "  logic clk;\n"
                               "  specify\n"
                               "    $recovery(posedge rst, posedge clk, 22);\n"
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

// §31.3.5: `rst` rises at time 302 and `clk` rises at time 312, so the window
// runs from 302 to 324 and the data transition stands 10 time units inside it
// against a limit of 22.
TEST(DrivenTimingCheckEvaluation, RecoveryViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #302 rst = 1'b1;\n"
                      "    #10 clk = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$recovery violation: data signal", 0, "31.3.5"));
}

// §31.3.5 again, and the same design: only the stimulus changes. `rst` rises at
// time 345 and `clk` rises at time 382, so the window runs from 345 to 367 and
// the data transition at 382 stands after it closes.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $recovery site can make about any design carries this substring
// and there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, RecoverySatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #345 rst = 1'b1;\n"
                      "    #37 clk = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$recovery violation: data signal"), nullptr);
}

}  // namespace
