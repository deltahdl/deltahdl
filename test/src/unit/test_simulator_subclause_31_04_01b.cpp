// Whether a running design's $skew check is evaluated against the stimulus that
// design drives, and what a violation then produces: a report on the DiagEngine
// the run holds.
//
// Every case here writes a design, drives its two signals from an initial
// block, and reads back the diagnostics standing on the fixture. No case builds
// a TimingCheckEntry, and none calls SpecifyManager::CheckSkewViolation or
// SkewChecker. That is what separates this file from
// test_simulator_subclause_31_04_01a.cpp beside it: every case there hands the
// predicate or the checker a reference time, a data time and a limit and asks
// for the verdict, so each proves the verdict is right once something asks and
// none proves that anything asks. Issue #3409 is that nothing did -- every
// caller of those in the tree was a unit test, so no §31.4.1 violation was ever
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
// when the design gains or loses a line above the $skew.
//
// §31.4.1 measures how far apart two signals move rather than placing one
// signal's transition inside a window the other bounds. Table 31-7 makes the
// reference event the timestamp and the data event the timecheck, and the check
// reports when
//
//   (timecheck time) - (timestamp time) > limit
//
// so there is no data-versus-reference asymmetry of the kind §31.3's stability
// windows carry, and a driver written for §31.3's shape does not reach this
// rule.
//
// §31.4.1 is event-based: "it is evaluated only after a data event. If there is
// never a data event ..., the $skew timing check shall never be evaluated, and
// no timing violation shall ever be reported." That is what
// SkewReferenceWithNoDataEventInARunReportsNothing below drives, and it is what
// separates $skew from §31.4.2's $timeskew, whose timer-based default reports
// once the limit elapses with no data event at all.
//
// The three cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to all
// three: a driver that reported unconditionally would fail the two quiet cases,
// and a driver that reported nothing would fail the violating one.
//
// The message substring stops before the signal name the report goes on to
// spell. What the violating case claims is that the violation was found and
// named as §31.4.1's, and naming a signal in the substring would tie it to
// which field each reached the report through as well.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.3.6 and §31.4.2
// through §31.4.6 beside this one. The limit is 46, not the 0 a
// TimingCheckEntry::limit holds before a limit expression has been evaluated
// into it. The violating case leaves 71 time units between the transitions and
// the satisfied case 39, and the reference edges stand at times 502, 530 and
// 566, so a case that read its interval, its limit or its edge out of another
// case's design would compare two numbers that disagree rather than two that
// coincide.
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
// Syntax 31-9 writes `$skew(reference_event, data_event, timing_check_limit
// [, notifier])`, the reference event first. `ref_sig` is not spelled `ref`,
// which Table B.1 reserves.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The design every case here runs, up to the point the stimulus is spliced in.
// It is a named constant rather than a literal inside the call below so that a
// case can name the line its $skew stands on with LineHolding
// (lib/cpp/test_helpers/helpers_reported_error.h). The stimulus follows the
// check, so a line of this text is that line of the whole source.
constexpr const char* kDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  specify\n"
    "    $skew(posedge ref_sig, posedge data_sig, 46);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

// Elaborates, lowers and runs the one design these cases share, with `stimulus`
// as the body of its initial block. False when the source did not elaborate
// cleanly, which a case asserts on before reading anything off the fixture: a
// design rejected before it ran says nothing about §31.4.1 whatever the case
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

// §31.4.1: `ref_sig` rises at time 502 and `data_sig` rises at time 573, so the
// data signal follows the reference by 71 time units against a limit of 46.
TEST(DrivenTimingCheckEvaluation, SkewViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #502 ref_sig = 1'b1;\n"
                      "    #71 data_sig = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$skew violation: data signal",
      LineHolding(kDesignBeforeStimulus, "$skew(posedge ref_sig"), "31.4.1"));
}

// §31.4.1 again, and the same design: only the stimulus changes. `ref_sig`
// rises at time 530 and `data_sig` rises at time 569, so the data signal
// follows the reference by 39 time units against the same limit of 46.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $skew site can make about any design carries this substring and
// there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, SkewSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #530 ref_sig = 1'b1;\n"
                      "    #39 data_sig = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

// §31.4.1's event-based rule: `ref_sig` rises at time 566 and `data_sig` never
// rises at all, so the check is never evaluated however much time elapses. A
// driver that started a timer at the reference edge would have scheduled the
// report for time 612 and the scheduler would have reached it, there being no
// later event to outlive; that timer is §31.4.2's default and not this clause's
// rule.
TEST(DrivenTimingCheckEvaluation,
     SkewReferenceWithNoDataEventInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus("    #566 ref_sig = 1'b1;\n", f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

}  // namespace
