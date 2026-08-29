// Whether a running design's $timeskew check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Every case here writes a design, drives its signals from an initial block,
// and reads back the diagnostics standing on the fixture. No case builds a
// TimingCheckEntry, and none calls SpecifyManager::CheckTimeskewViolation,
// ReportsTimeskewViolation or TimeskewChecker. That is what separates this file
// from test_simulator_subclause_31_04_02a.cpp beside it: every case there hands
// the predicate or the checker a reference time, a data time and a limit and
// asks for the verdict, so each proves the verdict is right once something asks
// and none proves that anything asks. Issue #3409 is that nothing did -- every
// caller of those in the tree was a unit test, so no §31.4.2 violation was ever
// reported out of a run.
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
// when the design gains or loses a line above the $timeskew.
//
// §31.4.2 makes the reference event the timestamp and the data event the
// timecheck -- Table 31-8 -- and reports when
//
//   (timecheck time) - (timestamp time) > limit
//
// The default behavior is timer-based: "a violation shall be reported
// immediately upon an elapse of time after the reference event equal to the
// limit", whether or not a data event ever arrives, and the check is dormant
// afterwards. A data event within the limit reports nothing and turns the check
// dormant at once. That default is what every case below is written on, and it
// is what separates §31.4.2 from §31.4.1's $skew, which is event-based and
// reports nothing when no data event ever comes.
//
// The first two cases share one design and differ in their stimulus alone.
// That is what shows a check being run rather than one answer being handed to
// both: a driver that reported unconditionally would fail the satisfied case,
// and a driver that reported nothing would fail the violating one.
//
// The violating case drives its data edge late rather than omitting it, so the
// case reports under the timer-based default -- the limit elapses at time 653
// with nothing having arrived -- and under the event-based reading the
// event_based_flag selects, where the data edge at 688 is what reports. A run
// that ends at the reference edge would leave the two readings disagreeing
// about whether the scheduler ever reached the elapse.
//
// The message substring stops before the signal name the report goes on to
// spell. What the violating case claims is that the violation was found and
// named as §31.4.2's, and naming a signal in the substring would tie it to
// which field each reached the report through as well.
//
// The last two cases share a second design, and in both of them the reference
// event and the data event fall at one simulation time. §31.4.2 decides that
// case within the timer-based default: "if a data event occurs within the
// limit, then a violation shall not be reported, and the check shall become
// dormant immediately". A data event no time at all after the reference event
// is one that occurs within the limit, so the check ends dormant and reports
// nothing. Both cases claim that, and neither tolerates a report.
//
// Issue #3421 is the defect the pair covers. A watcher runs as part of the
// commit that woke it, so a $timeskew whose two signals transitioned in one
// time step was left in a different state according to which driver committed
// first. With the reference signal committed first, OnTimestampEvent
// (src/simulator/timing_check_skew.cpp) opened a window and armed a timer at
// reference+limit, and the data event then ran OnTimeskewDataEvent in that same
// file, which closes the window and cancels the timer, so the check ended
// dormant and reported nothing. With the data signal committed first,
// OnTimeskewDataEvent closed whatever was open and OnTimestampEvent then opened
// a window and armed a timer, so the check ended armed and reported at
// reference+limit. ApplySlotEvents, again in that file, now applies the
// reference event before the data event once the slot's active and reactive
// region sets are drained, and ScheduleTimingCheckEvaluation
// (src/simulator/timing_check_driver_internal.h) is what defers it to
// Region::kPrePostponed.
//
// Each of those two cases writes its two assignments as two statements of one
// initial block with no delay between them. That is what makes the order the
// two signals commit in explicit and deterministic. A pair of continuous
// assignments would leave that order to the order the two were lowered in. The
// two cases differ in that order and in nothing else, which is what makes them
// say the answer follows the times the design gives the two events rather than
// the order the two assignments were written in.
//
// Both of those cases carry the run past reference+limit, on a third signal
// `tail_sig` that neither event of the $timeskew names. A timer left armed
// fires at reference+limit, so a run ending at the two transitions would report
// nothing whatever state the check was left in and neither case could fail.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.4.1 and §31.4.3
// through §31.4.6 beside this one. The limit is 52, not the 0 a
// TimingCheckEntry::limit holds before a limit expression has been evaluated
// into it. The violating case leaves 87 time units between the transitions and
// the satisfied case 43, and the reference edges stand at times 601 and 640, so
// a case that read its interval, its limit or its edge out of another case's
// design would compare two numbers that disagree rather than two that coincide.
//
// The second design carries a limit of 58, its two transitions both stand at
// time 667, and its trailing transition follows 94 time units later at time
// 761. None of those three numbers is a limit or a time the first two cases
// use, so a case that read a limit or an edge out of the other design would
// again compare two numbers that disagree. The limit is not 0. The timer is
// armed at reference+limit, and at a limit of 0 that expiry is the very time
// the two transitions stand at, so the run holds no moment after the expiry at
// which a timer left armed and a check turned dormant differ and the pair would
// claim nothing about a timer surviving the data event. At 58 the expiry stands
// at time 725, which is after the transitions and before the trailing
// transition the run is carried to.
//
// Each source drives every signal it declares to a known level before any
// transition that matters. §31.5 makes posedge the shorthand for edge[01, 0x,
// x1], so the x-to-0 assignments at time 0 are no posedge and the timeline of
// each case begins at the first delay.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.
//
// Syntax 31-10 writes `$timeskew(reference_event, data_event,
// timing_check_limit [, notifier][, event_based_flag][, remain_active_flag])`,
// the reference event first. No flag is written here, so the declaration takes
// §31.4.2's default. `ref_sig` is not spelled `ref`, which Table B.1 reserves.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The design every case here runs, up to the point the stimulus is spliced in.
// It is a named constant rather than a literal inside the call below so that a
// case can name the line its $timeskew stands on with LineHolding
// (lib/cpp/test_helpers/helpers_reported_error.h). The stimulus follows the
// check, so a line of this text is that line of the whole source.
constexpr const char* kDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig, posedge data_sig, 52);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

// The design the two simultaneous cases run, up to the point the stimulus is
// spliced in. It differs from kDesignBeforeStimulus in its limit and in the
// third signal `tail_sig`, which the $timeskew names in neither of its events
// and which is there to carry the run past the expiry a timer armed at the
// reference event would fire at.
constexpr const char* kSimultaneousDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  logic tail_sig;\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig, posedge data_sig, 58);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    tail_sig = 1'b0;\n";

// Elaborates, lowers and runs `design` with `stimulus` as the rest of the body
// of its initial block. False when the source did not elaborate cleanly, which
// a case asserts on before reading anything off the fixture: a design rejected
// before it ran says nothing about §31.4.2 whatever the case was written to
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

// §31.4.2: `ref_sig` rises at time 601 and `data_sig` does not rise until time
// 688, so the 52 the limit allows elapses at 653 with the data signal still
// where it was.
TEST(DrivenTimingCheckEvaluation, TimeskewViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #601 ref_sig = 1'b1;\n"
                              "    #87 data_sig = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$timeskew violation: data signal",
      LineHolding(kDesignBeforeStimulus, "$timeskew(posedge ref_sig"),
      "31.4.2"));
}

// §31.4.2 again, and the same design: only the stimulus changes. `ref_sig`
// rises at time 640 and `data_sig` rises at time 683, 43 time units later and
// so inside the 52 the limit allows, which reports nothing and turns the check
// dormant before the elapse it would otherwise report at.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $timeskew site can make about any design carries this substring
// and there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, TimeskewSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #640 ref_sig = 1'b1;\n"
                              "    #43 data_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$timeskew violation: data signal"), nullptr);
}

// §31.4.2: "if a data event occurs within the limit, then a violation shall not
// be reported, and the check shall become dormant immediately". `ref_sig` and
// `data_sig` both rise at time 667, the reference signal being assigned first,
// and the data event is therefore one that occurs within the 58 the limit
// allows. `tail_sig` rises at time 761, which carries the run past the time 725
// a timer armed at the reference event would report at.
//
// Absence is the claim, as it is in TimeskewSatisfiedInARunReportsNothing
// above, and a null FindDiag is the form for it.
TEST(DrivenTimingCheckEvaluation,
     TimeskewSimultaneousEventsWithReferenceAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #667 ref_sig = 1'b1;\n"
                              "    data_sig = 1'b1;\n"
                              "    #94 tail_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$timeskew violation: data signal"), nullptr);
}

// §31.4.2's within-the-limit sentence again, with the data signal `data_sig`
// assigned first. This case and
// TimeskewSimultaneousEventsWithReferenceAssignedFirstReportNothing above
// differ in the order of two assignments at one simulation time and in nothing
// else, which is what makes the two of them say the answer follows the times
// the design gives the two events rather than the order the two assignments
// were written in. This is the order issue #3421 left the check armed in, so
// this is the case that fails under the driver that issue names: the timer
// armed at time 725 was never cancelled and reported there.
TEST(DrivenTimingCheckEvaluation,
     TimeskewSimultaneousEventsWithDataAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #667 data_sig = 1'b1;\n"
                              "    ref_sig = 1'b1;\n"
                              "    #94 tail_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$timeskew violation: data signal"), nullptr);
}

}  // namespace
