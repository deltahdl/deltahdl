// Whether a running design's $timeskew check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Both cases here write a design, drive its two signals from an initial block,
// and read back the diagnostics standing on the fixture. Neither builds a
// TimingCheckEntry, and neither calls SpecifyManager::CheckTimeskewViolation,
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
// dormant at once. That default is what the two cases below are written on, and
// it is what separates §31.4.2 from §31.4.1's $skew, which is event-based and
// reports nothing when no data event ever comes.
//
// The two cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to both: a
// driver that reported unconditionally would fail the satisfied case, and a
// driver that reported nothing would fail the violating one.
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
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.4.1 and §31.4.3
// through §31.4.6 beside this one. The limit is 52, not the 0 a
// TimingCheckEntry::limit holds before a limit expression has been evaluated
// into it. The violating case leaves 87 time units between the transitions and
// the satisfied case 43, and the reference edges stand at times 601 and 640, so
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

// Elaborates, lowers and runs the one design these cases share, with `stimulus`
// as the body of its initial block. False when the source did not elaborate
// cleanly, which a case asserts on before reading anything off the fixture: a
// design rejected before it ran says nothing about §31.4.2 whatever the case
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

// §31.4.2: `ref_sig` rises at time 601 and `data_sig` does not rise until time
// 688, so the 52 the limit allows elapses at 653 with the data signal still
// where it was.
TEST(DrivenTimingCheckEvaluation, TimeskewViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #601 ref_sig = 1'b1;\n"
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
  ASSERT_TRUE(
      RanWithStimulus("    #640 ref_sig = 1'b1;\n"
                      "    #43 data_sig = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$timeskew violation: data signal"), nullptr);
}

}  // namespace
