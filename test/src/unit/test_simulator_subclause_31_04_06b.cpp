// Whether a running design's $nochange check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Both cases here write a design, drive its two signals from an initial block,
// and read back the diagnostics standing on the fixture. Neither builds a
// TimingCheckEntry, and neither calls SpecifyManager::CheckNochangeViolation.
// That is what separates this file from test_simulator_subclause_31_04_06a.cpp
// beside it: every case there hands the predicate two reference times, a data
// time and two offsets and asks for the verdict, so each proves the verdict is
// right once something asks and none proves that anything asks. Issue #3409 is
// that nothing did -- every caller of that predicate in the tree was a unit
// test, so no §31.4.6 violation was ever reported out of a run.
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
// when the design gains or loses a line above the $nochange.
//
// §31.4.6 "reports a timing violation if the data event occurs during the
// specified level of the control signal (the reference event)", so both edges
// of the reference bound the window where §31.3's stability windows use one
// edge of the reference and one of the data signal. The reference here is a
// posedge, and §31.4.6 says of that case that "the duration is the period
// during which the reference signal is high".
//
// The two cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to both: a
// driver that reported unconditionally would fail the satisfied case, and a
// driver that reported nothing would fail the violating one.
//
// Both edge offsets are written as 0, and no case here turns on them. Issue
// #3418 is why: a declared offset never reaches the registered check, because
// BuildTimingCheckUnderOptions in src/simulator/specify_timing_check.cpp never
// assigns TimingCheckEntry::start_edge_offset or
// TimingCheckEntry::end_edge_offset and Parser::ParseTimingCheckTrailingArgs
// puts both offsets into the same limits list as a limit, whence one is written
// to TimingCheckEntry::limit and the other to ::limit2 and neither is read. A
// case whose expected answer depended on a non-zero declared offset would fail
// on that defect rather than on §31.4.6, so §31.4.6's rule that "the start edge
// and end edge offsets can expand or shrink the timing violation region" is
// left uncovered here and the window each case below assumes is exactly the
// leading to the trailing reference edge. Syntax 31-14 makes both offsets
// mandatory, so they are written rather than omitted.
//
// The message substring stops before the signal name the report goes on to
// spell. What the violating case claims is that the violation was found and
// named as §31.4.6's, and naming a signal in the substring would tie it to
// which field each reached the report through as well.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.4.5 beside this
// one. The violating case puts its data transition 12 time units after the
// leading reference edge and 20 before the trailing one, and the satisfied case
// puts its data transition 96 time units after a trailing reference edge that
// stands 41 after the leading one, so no interval of either case is any
// interval of the other. The leading reference edges stand at times 1204 and
// 1250. So a case that read its interval or its edge out of another case's
// design would compare two numbers that disagree rather than two that coincide.
//
// Each source drives both signals to a known level before either transition
// that matters. §31.5 makes posedge the shorthand for edge[01, 0x, x1], so the
// x-to-0 assignments at time 0 open no window; the negedge the reference does
// answer to there closes none, no window having been opened before it.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.
//
// Syntax 31-14 writes `$nochange(reference_event, data_event,
// start_edge_offset, end_edge_offset [, notifier])`, the reference event first,
// and §31.4.6 requires that reference event use posedge or negedge rather than
// an edge-control specifier. The data event carries no edge, which §31.2's
// Syntax 31-2 allows and which no edge restricts.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The design every case here runs, up to the point the stimulus is spliced in.
// It is a named constant rather than a literal inside the call below so that a
// case can name the line its $nochange stands on with LineHolding
// (lib/cpp/test_helpers/helpers_reported_error.h). The stimulus follows the
// check, so a line of this text is that line of the whole source.
constexpr const char* kDesignBeforeStimulus =
    "module top;\n"
    "  logic ctl;\n"
    "  logic d;\n"
    "  specify\n"
    "    $nochange(posedge ctl, d, 0, 0);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ctl = 1'b0;\n"
    "    d = 1'b0;\n";

// Elaborates, lowers and runs the one design these cases share, with `stimulus`
// as the body of its initial block. False when the source did not elaborate
// cleanly, which a case asserts on before reading anything off the fixture: a
// design rejected before it ran says nothing about §31.4.6 whatever the case
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

// §31.4.6: `ctl` rises at time 1204 and falls at time 1236, and `d` rises at
// time 1216, inside the window those two edges bound.
TEST(DrivenTimingCheckEvaluation, NochangeViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #1204 ctl = 1'b1;\n"
                      "    #12 d = 1'b1;\n"
                      "    #20 ctl = 1'b0;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$nochange violation: data signal",
      LineHolding(kDesignBeforeStimulus, "$nochange(posedge ctl"), "31.4.6"));
}

// §31.4.6 again, and the same design: only the stimulus changes. `ctl` rises at
// time 1250 and falls at time 1291, and `d` rises at time 1387, after the
// window those two edges bound has closed.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $nochange site can make about any design carries this substring
// and there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, NochangeSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #1250 ctl = 1'b1;\n"
                      "    #41 ctl = 1'b0;\n"
                      "    #96 d = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

}  // namespace
