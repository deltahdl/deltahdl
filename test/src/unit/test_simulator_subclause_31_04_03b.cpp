// Whether a running design's $fullskew check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Both cases here write a design, drive its two signals from an initial block,
// and read back the diagnostics standing on the fixture. Neither builds a
// TimingCheckEntry, and neither calls SpecifyManager::CheckFullskewViolation,
// ReportsFullskewViolation or FullskewSecondTimestampAction. That is what
// separates this file from test_simulator_subclause_31_04_03a.cpp beside it:
// every case there hands a predicate a reference time, a data time and a limit
// and asks for the verdict, so each proves the verdict is right once something
// asks and none proves that anything asks. Issue #3409 is that nothing did --
// every caller of those in the tree was a unit test, so no §31.4.3 violation
// was ever reported out of a run.
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
// when the design gains or loses a line above the $fullskew.
//
// §31.4.3 is §31.4.2's check with the two signals allowed to transition in
// either order. Which is the timestamp is decided by which moved first, and
// which limit applies follows from that: "the first limit is the maximum time
// by which the data event should follow the reference event. The second limit
// is the maximum time by which the reference event should follow the data
// event." The check reports when
//
//   (timecheck time) - (timestamp time) > limit
//
// with limit set to limit1 when the reference transitions first. Both cases
// below move the reference first, so limit1 is the one that decides them.
//
// The two cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to both: a
// driver that reported unconditionally would fail the satisfied case, and a
// driver that reported nothing would fail the violating one.
//
// The message substring stops before the signal names the report goes on to
// spell. §31.4.3's message names both signals and neither is "the data signal",
// the roles being decided by transition order rather than by argument position,
// so the substring here is the one the report opens with and nothing more.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.4.2 and §31.4.4
// through §31.4.6 beside this one. The limits are 29 (limit1) and 64 (limit2),
// neither of them the 0 a TimingCheckEntry::limit holds before a limit
// expression has been evaluated into it. The violating case leaves 49 time
// units between the transitions, which is outside the 29 limit1 allows and
// inside the 64 limit2 allows, so a driver that read limit2 where limit1
// belongs reports nothing and the case fails. The satisfied case leaves 26, and
// the reference edges stand at times 703 and 740, so a case that read its
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
// Syntax 31-11 writes `$fullskew(reference_event, data_event,
// timing_check_limit, timing_check_limit [, notifier][, event_based_flag]
// [, remain_active_flag])`, the reference event first and limit1 before limit2.
// No flag is written here, so the declaration takes §31.4.3's timer-based
// default; the violating case drives its data edge after the elapse rather than
// omitting it, so it reports under that default and under the event-based
// reading alike. `ref_sig` is not spelled `ref`, which Table B.1 reserves.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The design every case here runs, up to the point the stimulus is spliced in.
// It is a named constant rather than a literal inside the call below so that a
// case can name the line its $fullskew stands on with LineHolding
// (lib/cpp/test_helpers/helpers_reported_error.h). The stimulus follows the
// check, so a line of this text is that line of the whole source.
constexpr const char* kDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig, posedge data_sig, 29, 64);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

// Elaborates, lowers and runs the one design these cases share, with `stimulus`
// as the body of its initial block. False when the source did not elaborate
// cleanly, which a case asserts on before reading anything off the fixture: a
// design rejected before it ran says nothing about §31.4.3 whatever the case
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

// §31.4.3: `ref_sig` rises at time 703 and `data_sig` rises at time 752, so the
// two signals move 49 time units apart against the 29 limit1 allows the data
// signal to trail the reference by.
TEST(DrivenTimingCheckEvaluation, FullskewViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #703 ref_sig = 1'b1;\n"
                      "    #49 data_sig = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$fullskew violation: signals",
      LineHolding(kDesignBeforeStimulus, "$fullskew(posedge ref_sig"),
      "31.4.3"));
}

// §31.4.3 again, and the same design: only the stimulus changes. `ref_sig`
// rises at time 740 and `data_sig` rises at time 766, 26 time units later and
// so inside the 29 limit1 allows.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $fullskew site can make about any design carries this substring
// and there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, FullskewSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #740 ref_sig = 1'b1;\n"
                      "    #26 data_sig = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

}  // namespace
