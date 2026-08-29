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
// than ReportedError. The report stands on the line the check was written on.
// TimingCheckEntry::loc (src/simulator/specify_timing_check.h) carries that
// position: Parser::ParseTimingCheck (src/parser/parser_specify.cpp) records
// the check's own first token into it, and BuildTimingCheckUnderOptions
// (src/simulator/specify_timing_check.cpp) copies it across. Issue #3414 was
// that the report stood at SourceLoc::None(), whose line is 0, because nothing
// carried that position from the declaration to the run. Each case below names
// the line through LineHolding (lib/cpp/test_helpers/helpers_reported_error.h),
// which reads it off the design text, rather than writing a number down. A
// number goes stale the moment the design gains or loses a line above the
// check.
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
// The first three cases share one design and differ in their stimulus alone.
// That is what shows a check being run rather than one answer being handed to
// all three: a driver that reported unconditionally would fail the satisfied
// case, and a driver that reported nothing would fail the two violating ones.
//
// The last two cases share a second design, and in both of them the reference
// event and the data event fall at one simulation time. §31.3.6 states the
// verdict for that outright: "The $recrem check shall report a timing violation
// when the reference and data events occur simultaneously". Nothing tested that
// sentence before, and the two cases pin it from both of the orders the clause
// says the verdict must not depend on: "when both the removal limit and the
// recovery limit are positive, either the reference event or the data event can
// be the timecheck event. It shall depend upon which occurs first in the
// simulation".
//
// Neither case is regression coverage for issue #3415, and neither would have
// failed under the driver that issue names. A $recrem is evaluated at whichever
// of its two events occurs first, so both watchers ask for an evaluation, and
// the second of the two to run under that driver had both times recorded
// whichever order the two committed in. The $hold pair in
// test_simulator_subclause_31_03_01b.cpp is what catches the defect, $hold
// being evaluated at one of its two events alone.
//
// Each of those two cases writes its two assignments as two statements of one
// initial block with no delay between them. That is what makes the order the
// two signals commit in explicit and deterministic. A pair of continuous
// assignments would leave that order to the order the two were lowered in.
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
// The two simultaneous cases run a second design, whose limits are 45
// (recovery) and 27 (removal) and whose two transitions both stand at time 466.
// None of those three numbers is a limit or a time the first three cases use,
// so a case that read a limit or an edge out of the other design would again
// compare two numbers that disagree. Neither limit is 0, which is the condition
// §31.3.6 states the simultaneous rule under: TwoSidedWindowViolated
// (src/simulator/timing_check_stability.cpp) reports nothing at all for a check
// whose two limits are zero, so a zero limit would make both cases pass without
// the simultaneous rule holding. A simultaneous pair is read against the limit
// bounding the side the window ends on, which for $recrem is the removal limit:
// LimitsOf in that same file puts TimingCheckEntry::limit2 there, and
// TwoSidedWindowViolated compares against it whenever the data event does not
// follow the reference event.
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

// The design the first three cases run, up to the stimulus each case supplies.
// A case hands it to LineHolding, which reads the line the `$recrem` keyword
// stands on out of this text. The declaration stands above the stimulus, so the
// line it holds here is the line it holds in the whole source.
constexpr const char* kDesignThroughTheCheck =
    "module top;\n"
    "  logic clr;\n"
    "  logic clk;\n"
    "  specify\n"
    "    $recrem(posedge clr, posedge clk, 24, 14);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clr = 1'b0;\n"
    "    clk = 1'b0;\n";

// The design the two simultaneous cases run, up to the stimulus each of them
// supplies. It differs from kDesignThroughTheCheck in its two limits alone, and
// LineHolding reads the `$recrem` line off it the same way.
constexpr const char* kSimultaneousDesignThroughTheCheck =
    "module top;\n"
    "  logic clr;\n"
    "  logic clk;\n"
    "  specify\n"
    "    $recrem(posedge clr, posedge clk, 45, 27);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clr = 1'b0;\n"
    "    clk = 1'b0;\n";

// Elaborates, lowers and runs `design` with `stimulus` as the rest of the body
// of its initial block. False when the source did not elaborate cleanly, which
// a case asserts on before reading anything off the fixture: a design rejected
// before it ran says nothing about §31.3.6 whatever the case was written to
// expect.
bool RanWithStimulus(const char* design, const std::string& stimulus,
                     SimFixture& f) {
  auto* rtl = ElaborateSrc(std::string(design) + stimulus +
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
  ASSERT_TRUE(RanWithStimulus(kDesignThroughTheCheck,
                              "    #404 clr = 1'b1;\n"
                              "    #19 clk = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$recrem violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$recrem(posedge clr"), "31.3.6"));
}

// §31.3.6, removal side: the window ends at the reference edge and opens
// `removal_limit` time units before it, running backwards where the recovery
// side's runs forwards. `clk` rises at time 436 and `clr` rises at time 438,
// leaving 2 time units against a removal limit of 14.
TEST(DrivenTimingCheckEvaluation, RecremRemovalSideViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignThroughTheCheck,
                              "    #436 clk = 1'b1;\n"
                              "    #2 clr = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$recrem violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$recrem(posedge clr"), "31.3.6"));
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
  ASSERT_TRUE(RanWithStimulus(kDesignThroughTheCheck,
                              "    #450 clr = 1'b1;\n"
                              "    #38 clk = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$recrem violation: data signal"), nullptr);
}

// §31.3.6: "The $recrem check shall report a timing violation when the
// reference and data events occur simultaneously." The reference event and the
// data event both stand at time 466, the reference signal `clr` being assigned
// first, and the two limits are the 45 and the 27 the clause requires to be
// positive for the sentence to apply.
TEST(DrivenTimingCheckEvaluation,
     RecremSimultaneousEventsWithReferenceAssignedFirstAreReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignThroughTheCheck,
                              "    #466 clr = 1'b1;\n"
                              "    clk = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$recrem violation: data signal",
      LineHolding(kSimultaneousDesignThroughTheCheck, "$recrem(posedge clr"),
      "31.3.6"));
}

// §31.3.6's simultaneous sentence again, with the data signal `clk` assigned
// first. This case and
// RecremSimultaneousEventsWithReferenceAssignedFirstAreReported above differ in
// the order of two assignments at one simulation time and in nothing else,
// which is what makes the two of them say the verdict follows the times the
// design gives the two events rather than the order the assignments were
// written in.
TEST(DrivenTimingCheckEvaluation,
     RecremSimultaneousEventsWithDataAssignedFirstAreReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignThroughTheCheck,
                              "    #466 clk = 1'b1;\n"
                              "    clr = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$recrem violation: data signal",
      LineHolding(kSimultaneousDesignThroughTheCheck, "$recrem(posedge clr"),
      "31.3.6"));
}

}  // namespace
