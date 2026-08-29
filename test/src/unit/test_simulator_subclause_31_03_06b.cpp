// Whether a running design's $recrem check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Every case here writes a design, drives its two signals from an initial
// block, and reads back the diagnostics standing on the fixture. No case builds
// a TimingCheckEntry, and none calls SpecifyManager::CheckRecremViolation. That
// is what separates this file from test_simulator_subclause_31_03_06a.cpp
// beside it: every case there hands the predicate a reference time, a data time
// and two limits and asks for the verdict, so each proves the verdict is right
// once something asks and none proves that anything asks. Issue #3409 is that
// nothing did -- every caller of that predicate in the tree was a unit test, so
// no §31.3.6 violation was ever reported out of a run.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportTimingViolation in src/simulator/timing_check_driver_internal.h calls
// DiagEngine::Warning; the cases below read it through ReportedWarning rather
// than ReportedError. It stands at SourceLoc::None(), whose line is 0, because
// TimingCheckEntry records no position for the declaration it was built from.
//
// One $recrem declaration stands for two constraints. §31.3.6 makes
//
//   $recrem(posedge clr, posedge clk, tREC, tREM)
//
// equivalent to $removal(posedge clr, posedge clk, tREM) with
// $recovery(posedge clr, posedge clk, tREC), so a clk edge inside tREM before
// the clr edge violates the removal side -- §31.3.4's window, which ends at the
// reference -- and one inside tREC after that edge violates the recovery side,
// §31.3.5's window, which begins there. The two violating cases below drive one
// side each, which is why they are two cases and not one: a driver that checked
// only one side would report nothing for the case written for the other, and
// both would pass a case that drove both sides at once.
//
// The three cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to all
// three: a driver that reported unconditionally would fail the satisfied case,
// and a driver that reported nothing would fail the two violating ones.
//
// The message substring stops before the signal name the report goes on to
// spell, and the two sides of the window share it. What each case claims is
// that a §31.3.6 violation was found for the stimulus it drove, and the
// stimulus is what says which side found it.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.3.5 and §31.4.1
// through §31.4.6 beside this one. The limits are 24 (recovery) and 14
// (removal), neither of them the 0 a TimingCheckEntry::limit holds before a
// limit expression has been evaluated into it. The recovery-side case leaves 19
// time units between the transitions, which is inside the 24 the recovery side
// allows and outside the 14 the removal side does, so a driver that read the
// removal limit where the recovery limit belongs reports nothing and the case
// fails. The removal-side case leaves 2 and the satisfied case 38, and the
// `clr` edges stand at times 404, 438 and 450, so a case that read its
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
// Syntax 31-8 writes `$recrem(reference_event, data_event, timing_check_limit,
// timing_check_limit, ...)` with the recovery limit before the removal limit,
// the reference event first, and §31.3.6's worked equivalence names that
// reference event `clear` and the data event a clock.

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
// design rejected before it ran says nothing about §31.3.6 whatever the case
// was written to expect.
bool RanWithStimulus(const std::string& stimulus, SimFixture& f) {
  auto* rtl = ElaborateSrc(
      std::string("module top;\n"
                  "  logic clr;\n"
                  "  logic clk;\n"
                  "  specify\n"
                  "    $recrem(posedge clr, posedge clk, 24, 14);\n"
                  "  endspecify\n"
                  "  initial begin\n"
                  "    clr = 1'b0;\n"
                  "    clk = 1'b0;\n") +
          stimulus +
          "  end\n"
          "endmodule\n",
      f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

// §31.3.6, recovery side: the window begins at the reference edge and closes
// `recovery_limit` time units after it. `clr` rises at time 404 and `clk` rises
// at time 423, leaving 19 time units against a recovery limit of 24.
TEST(DrivenTimingCheckEvaluation, RecremRecoverySideViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #404 clr = 1'b1;\n"
                      "    #19 clk = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$recrem violation: data signal", 0, "31.3.6"));
}

// §31.3.6, removal side: the window ends at the reference edge and opens
// `removal_limit` time units before it, running backwards where the recovery
// side's runs forwards. `clk` rises at time 436 and `clr` rises at time 438,
// leaving 2 time units against a removal limit of 14.
TEST(DrivenTimingCheckEvaluation, RecremRemovalSideViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #436 clk = 1'b1;\n"
                      "    #2 clr = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$recrem violation: data signal", 0, "31.3.6"));
}

// §31.3.6 again, and the same design: only the stimulus changes. `clr` rises at
// time 450 and `clk` rises at time 488, leaving 38 time units against a
// recovery limit of 24, and `clk` never transitions before the reference edge,
// so neither side of the window closes with anything inside it.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $recrem site can make about any design carries this substring and
// there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, RecremSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #450 clr = 1'b1;\n"
                      "    #38 clk = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$recrem violation: data signal"), nullptr);
}

}  // namespace
