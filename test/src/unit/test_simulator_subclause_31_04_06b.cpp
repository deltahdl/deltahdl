// Whether a running design's $nochange check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds. §31.4.6's two edge offsets are covered here as
// well, from the values a declaration writes through to the verdict a run
// reaches over them.
//
// Every case here writes a design, drives its signals from an initial block,
// and reads back what the run left standing on the fixture: the diagnostics on
// SimFixture::diag, or the check registered on the SpecifyManager
// SimContext::GetSpecifyManager answers with. No case builds a
// TimingCheckEntry, and none calls SpecifyManager::CheckNochangeViolation.
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
// Each violating case below names that line with LineHolding over the design it
// ran rather than writing a number, so the case cannot drift when the design
// gains or loses a line above the $nochange.
//
// §31.4.6 "reports a timing violation if the data event occurs during the
// specified level of the control signal (the reference event)", so both edges
// of the reference bound the window where §31.3's stability windows use one
// edge of the reference and one of the data signal. The reference here is a
// posedge, and §31.4.6 says of that case that "the duration is the period
// during which the reference signal is high".
//
// §31.4.6 moves each end of that window by an offset the declaration writes:
// "(beginning of time window) = (leading reference edge time) -
// start_edge_offset" and "(end of time window) = (trailing reference edge time)
// + end_edge_offset". The clause "reports a timing violation in the following
// case: (beginning of time window) < (data event time) < (end of time window)".
// "The end points of the time window are not included." A positive offset
// extends the region and a negative one shrinks it, §31.4.6 saying of a
// negative end edge offset that it "shrinks the region by ending it earlier".
// "If both the offsets are zero, the size of the region shall not change."
//
// Two designs are run below. kDesignBeforeStimulus writes both offsets as 0 and
// neither case over it turns on them. kOffsetDesignBeforeStimulus writes 27 as
// the start edge offset and -14 as the end edge offset, and the seven cases
// over it are what cover the offsets: NochangeOffsetsAreRegisteredAsWritten
// reads both back off the registered TimingCheckEntry, and the six cases after
// it place a data transition where the offsets decide the verdict.
//
// Issue #3418 is why the first three of those were not here before. A declared
// offset never reached the registered check: BuildTimingCheckUnderOptions in
// src/simulator/specify_timing_check.cpp assigned neither
// TimingCheckEntry::start_edge_offset nor TimingCheckEntry::end_edge_offset,
// and Parser::ParseTimingCheckTrailingArgs in src/parser/parser_specify.cpp
// collects every trailing operand into TimingCheckDecl::limits by position, so
// one offset was written to TimingCheckEntry::limit and the other to ::limit2
// and neither was read. NochangeOffsetsAreRegisteredAsWritten asserts that
// limit and limit2 are 0 for that reason: landing the offsets where a limit is
// read is what the defect was, and §31.4.6's Syntax 31-14 writes no
// timing_check_limit for a $nochange to hold. Syntax 31-14 makes both offsets
// mandatory, so kDesignBeforeStimulus writes its two zeros rather than omitting
// them.
//
// NochangeStartEdgeOffsetWidensTheWindowIntoAViolation transitions `d` at the
// same simulation time as the leading reference edge, and after that edge in
// the initial block, rather than before it. Program order settles which watcher
// runs first: WriteVar in src/simulator/statement_assign_core.cpp commits a
// blocking assignment and calls Variable::NotifyWatchers before the next
// statement runs, so the watcher ArmNochangeWindow armed on `ctl` records the
// leading edge and the watcher it armed on `d` then records the data
// transition, both at that one time. That was the earliest placement any case
// could measure when it was written, a transition standing strictly before the
// leading reference edge being dropped rather than measured, and it is the
// earliest no longer:
// NochangeDataInsideTheStartOffsetIntervalIsReported below stands earlier
// still. A transition at the leading edge time turns on the start edge offset,
// §31.4.6 excluding the end points: at offset 0 the beginning of the window is
// the data event time and the check is satisfied, and at offset 27 the
// beginning stands 27 earlier and the same transition is inside.
//
// Issue #3424 is why the four cases after that one are here. §31.4.6 puts
// "(beginning of time window) = (leading reference edge time) -
// start_edge_offset", so a positive start edge offset opens the window before
// the leading reference edge that bounds it, and no violation standing in the
// interval that offset adds could ever be reported. RecordNochangeData in
// src/simulator/timing_check_pulse.cpp returned without recording a data
// transition while no leading edge had been seen, and the watcher
// ArmNochangeWindow arms on the leading edge cleared everything held, so a
// transition in that interval was gone before either end point of the window it
// fell in was known.
//
// Those four cases divide by which window opens over the transition and by
// where the transition stands against that window's beginning.
// NochangeDataInsideTheStartOffsetIntervalIsReported and
// NochangeDataAtTheWindowBeginningReportsNothing place the transition before
// the first leading reference edge of the run, inside the beginning in the one
// and exactly at it in the other.
// NochangeDataBeforeASecondLeadingEdgeIsReportedAgainstThatWindow and
// NochangeDataAtASecondWindowBeginningReportsNothing place it after a window
// has opened and closed and before the leading reference edge of the next,
// where it is measured against the closed window as it arrives and held for the
// window still to open. §31.4.6 makes both measurements owed: one transition
// standing inside two windows violates both.
//
// DropTransitionsBefore in src/simulator/timing_check_pulse.cpp is what decides
// the second pair. It keeps a held transition only where it stands strictly
// after "(leading reference edge time) - start_edge_offset" for the reference
// time it is given, and it is given the leading reference edge time at a
// leading edge and the current time at a data transition.
//
// NochangeViolationInARunIsReported and NochangeSatisfiedInARunReportsNothing
// share kDesignBeforeStimulus and differ in their stimulus alone, and
// NochangeStartEdgeOffsetWidensTheWindowIntoAViolation and
// NochangeDataOutsideTheWidenedWindowReportsNothing stand in that same relation
// over kOffsetDesignBeforeStimulus, as do
// NochangeDataInsideTheStartOffsetIntervalIsReported and
// NochangeDataAtTheWindowBeginningReportsNothing, and as do
// NochangeDataBeforeASecondLeadingEdgeIsReportedAgainstThatWindow and
// NochangeDataAtASecondWindowBeginningReportsNothing. Each of those two pairs
// differs in where the data transition stands against the beginning of the
// window and in nothing else: strictly after it in the one, exactly at it in
// the other. That is what
// shows a check being run rather than one answer being handed to both: a driver
// that reported unconditionally would fail the satisfied case, and a driver
// that reported nothing would fail the violating one.
//
// The message substring stops before the signal name the report goes on to
// spell. What a violating case claims is that the violation was found and named
// as §31.4.6's, and naming a signal in the substring would tie it to which
// field each reached the report through as well.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.4.5 beside this
// one. The violating case over kDesignBeforeStimulus puts its data transition
// 12 time units after the leading reference edge and 20 before the trailing
// one, and the satisfied case over it puts its data transition 96 time units
// after a trailing reference edge that stands 41 after the leading one, so no
// interval of either case is any interval of the other. Those leading reference
// edges stand at times 1204 and 1250, and the two over
// kOffsetDesignBeforeStimulus at 1327 and 1373. So a case that read its
// interval or its edge out of another case's design would compare two numbers
// that disagree rather than two that coincide.
//
// The four cases issue #3424 added stand later again.
// NochangeDataInsideTheStartOffsetIntervalIsReported transitions `d` at 1511,
// raises `ctl` at 1520 and drops it at 1583, so its window runs from 1493 to
// 1569 and its data transition stands 18 after the beginning of the window and
// 9 before the leading reference edge.
// NochangeDataAtTheWindowBeginningReportsNothing transitions `d` at 1604,
// raises `ctl` at 1631 and drops it at 1677.
// NochangeDataBeforeASecondLeadingEdgeIsReportedAgainstThatWindow raises `ctl`
// at 1706, drops it at 1751, transitions `d` at 1793, raises `ctl` again at
// 1803 and drops it at 1861, so its first window runs from 1679 to 1737 and its
// second from 1776 to 1847 and its data transition stands 56 after the end of
// the first, 17 after the beginning of the second and 10 before the leading
// reference edge that opens it.
// NochangeDataAtASecondWindowBeginningReportsNothing raises `ctl` at 1904,
// drops it at 1936, transitions `d` at 1971, raises `ctl` again at 1998 and
// drops it at 2049, so its first window runs from 1877 to 1922 and its second
// from 1971 to 2035.
//
// Three intervals below are written to coincide with a quantity rather than to
// differ from it, and each coincidence is what its case is about. One is the 0
// between the leading reference edge and the data transition of
// NochangeStartEdgeOffsetWidensTheWindowIntoAViolation. The other two are the
// 27 between the data transition and the leading reference edge after it in
// NochangeDataAtTheWindowBeginningReportsNothing and in
// NochangeDataAtASecondWindowBeginningReportsNothing, which is the start edge
// offset written a second time so that the transition stands exactly at the
// beginning of the window that edge opens.
//
// The two edge offsets are 27 and -14. They differ from each other, they differ
// in sign, and neither is any interval or any edge time a case writes, so a
// build that read one of them where the other was written, or read either into
// TimingCheckEntry::limit, answers with a number that disagrees.
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
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

// The design the two cases that turn on no edge offset run, up to the point the
// stimulus is spliced in. It is a named constant rather than a literal inside
// the call below so that a case can name the line its $nochange stands on with
// LineHolding (lib/cpp/test_helpers/helpers_reported_error.h). The stimulus
// follows the check, so a line of this text is that line of the whole source.
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

// The design the three cases that turn on §31.4.6's edge offsets run, written
// out beside the one above rather than derived from it so that each reads as
// the source its cases were written against. It differs from that one in its
// two offsets alone, 27 as the start edge offset and -14 as the end edge
// offset, and its $nochange stands on the same line.
constexpr const char* kOffsetDesignBeforeStimulus =
    "module top;\n"
    "  logic ctl;\n"
    "  logic d;\n"
    "  specify\n"
    "    $nochange(posedge ctl, d, 27, -14);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ctl = 1'b0;\n"
    "    d = 1'b0;\n";

// Elaborates, lowers and runs `design` with `stimulus` as the rest of the body
// of its initial block. False when the source did not elaborate cleanly, which
// a case asserts on before reading anything off the fixture: a design rejected
// before it ran says nothing about §31.4.6 whatever the case was written to
// expect.
bool RanWithStimulus(const std::string& design, const std::string& stimulus,
                     SimFixture& f) {
  auto* rtl = ElaborateSrc(design + stimulus +
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
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #1204 ctl = 1'b1;\n"
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
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #1250 ctl = 1'b1;\n"
                              "    #41 ctl = 1'b0;\n"
                              "    #96 d = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

// §31.4.6: the two edge offsets kOffsetDesignBeforeStimulus writes, read back
// off the check the run registered on SimContext::GetSpecifyManager. The
// stimulus is empty because the claim is about what the declaration registered,
// which no transition changes.
//
// TimingCheckEntry::limit and ::limit2 are 0 because §31.4.6's Syntax 31-14
// writes no timing_check_limit at all for a $nochange. Reading them is what
// says the two offsets did not also land in the fields a limit is read from,
// which is the form issue #3418 took.
TEST(DrivenTimingCheckEvaluation, NochangeOffsetsAreRegisteredAsWritten) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus, "", f));
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  ASSERT_NE(mgr, nullptr);
  ASSERT_EQ(mgr->GetTimingChecks().size(), 1U);
  const TimingCheckEntry& check = mgr->GetTimingChecks()[0];
  EXPECT_EQ(check.start_edge_offset, 27);
  EXPECT_EQ(check.end_edge_offset, -14);
  EXPECT_EQ(check.limit, 0U);
  EXPECT_EQ(check.limit2, 0U);
}

// §31.4.6 with the offsets kOffsetDesignBeforeStimulus writes: `ctl` rises at
// time 1327 and falls at time 1365, and `d` rises at time 1327 as well, after
// the leading reference edge in the initial block and at the same simulation
// time as it. The beginning of the window is 1327 - 27 = 1300 and its end is
// 1365 + (-14) = 1351, so 1300 < 1327 < 1351 and the data transition is inside.
//
// A start edge offset of 0 would put the beginning of the window at 1327, which
// is the data event time and which §31.4.6 excludes, so the verdict here turns
// on the offset having reached the check. A build that read the two offsets
// into each other's fields would put the beginning at 1341 and report nothing
// either.
TEST(DrivenTimingCheckEvaluation,
     NochangeStartEdgeOffsetWidensTheWindowIntoAViolation) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1327 ctl = 1'b1;\n"
                              "    d = 1'b1;\n"
                              "    #38 ctl = 1'b0;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$nochange violation: data signal",
      LineHolding(kOffsetDesignBeforeStimulus, "$nochange(posedge ctl"),
      "31.4.6"));
}

// §31.4.6 and the same design: only the stimulus changes. `ctl` rises at time
// 1373 and falls at time 1397, `d` rises at time 1449, and `ctl` rises again at
// time 1482. The window the first two edges bound ends at 1397 + (-14) = 1383,
// and the window the last edge opens begins at 1482 - 27 = 1455, so the data
// transition stands after the end of the one and before the beginning of the
// other and falls in neither.
//
// The transition is measured rather than passed over, which is what this case
// adds to the violating one above. RecordNochangeData in
// src/simulator/timing_check_pulse.cpp answers a data transition arriving after
// the trailing reference edge straight away, an end edge offset being able to
// extend the window past that edge, so NochangeWindowViolated read this
// transition against the window and declined it. A driver reporting on every
// data transition it was handed would report here.
TEST(DrivenTimingCheckEvaluation,
     NochangeDataOutsideTheWidenedWindowReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1373 ctl = 1'b1;\n"
                              "    #24 ctl = 1'b0;\n"
                              "    #52 d = 1'b1;\n"
                              "    #33 ctl = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

// §31.4.6 with the offsets kOffsetDesignBeforeStimulus writes: `d` rises at
// time 1511, `ctl` rises at time 1520 and falls at time 1583. The beginning of
// the window is 1520 - 27 = 1493 and its end is 1583 + (-14) = 1569, so
// 1493 < 1511 < 1569 and the data transition is inside.
//
// The data transition stands strictly between the beginning of the window and
// the leading reference edge that bounds it, which is the interval a positive
// start edge offset adds and which no case could reach before issue #3424 was
// fixed. RecordNochangeData in src/simulator/timing_check_pulse.cpp returned
// without recording a data transition while no leading edge had been seen, and
// the watcher on the leading edge cleared whatever was held, so this stimulus
// reported nothing wherever the transition was placed in that interval. That
// is why NochangeStartEdgeOffsetWidensTheWindowIntoAViolation above transitions
// `d` at the leading reference edge time instead: that was then the earliest
// placement a case could measure.
TEST(DrivenTimingCheckEvaluation,
     NochangeDataInsideTheStartOffsetIntervalIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1511 d = 1'b1;\n"
                              "    #9 ctl = 1'b1;\n"
                              "    #63 ctl = 1'b0;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$nochange violation: data signal",
      LineHolding(kOffsetDesignBeforeStimulus, "$nochange(posedge ctl"),
      "31.4.6"));
}

// §31.4.6 and the same design: only the stimulus changes. `d` rises at time
// 1604, `ctl` rises at time 1631 and falls at time 1677. The beginning of the
// window is 1631 - 27 = 1604, which is the data event time, and §31.4.6 says
// "the end points of the time window are not included", so the transition is
// outside the window and nothing is reported.
//
// The 27 between the data transition and the leading reference edge is the
// start edge offset written a second time, which is what stands the transition
// exactly at the beginning of the window rather than near it. §31.4.6 excludes
// that beginning in two places: DropTransitionsBefore in
// src/simulator/timing_check_pulse.cpp keeps a held transition only when it
// stands strictly after the beginning, and NochangeWindowViolated beside it
// requires "(beginning of time window) < (data event time)" of the transitions
// it is handed. This case claims the verdict §31.4.6 states and not which of
// those two reached it.
TEST(DrivenTimingCheckEvaluation,
     NochangeDataAtTheWindowBeginningReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1604 d = 1'b1;\n"
                              "    #27 ctl = 1'b1;\n"
                              "    #46 ctl = 1'b0;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

// §31.4.6 and the same design: `ctl` rises at time 1706, falls at time 1751,
// rises again at time 1803 and falls at time 1861, and `d` rises at time 1793.
// The first window runs from 1706 - 27 = 1679 to 1751 + (-14) = 1737 and the
// second from 1803 - 27 = 1776 to 1861 + (-14) = 1847. The data transition at
// 1793 stands after the end of the first window and inside the second, so a run
// that measured it against the first alone reports nothing and this case
// expects the violation the second window carries.
//
// The transition stands strictly between the beginning of the second window and
// the leading reference edge that opens it, which is where
// DropTransitionsBefore in src/simulator/timing_check_pulse.cpp decides. The
// transition is held from before that edge, the edge sets the reference time
// the drop measures back from, and 1793 stands 17 after the 1776 the drop keeps
// from. A run that held nothing across a closed window reports nothing here,
// the transition having been answered against the first window when it arrived
// and discarded.
TEST(DrivenTimingCheckEvaluation,
     NochangeDataBeforeASecondLeadingEdgeIsReportedAgainstThatWindow) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1706 ctl = 1'b1;\n"
                              "    #45 ctl = 1'b0;\n"
                              "    #42 d = 1'b1;\n"
                              "    #10 ctl = 1'b1;\n"
                              "    #58 ctl = 1'b0;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$nochange violation: data signal",
      LineHolding(kOffsetDesignBeforeStimulus, "$nochange(posedge ctl"),
      "31.4.6"));
}

// §31.4.6 and the same design: only the stimulus changes. `ctl` rises at time
// 1904, falls at time 1936, rises again at time 1998 and falls at time 2049,
// and `d` rises at time 1971. The first window runs from 1904 - 27 = 1877 to
// 1936 + (-14) = 1922 and the second from 1998 - 27 = 1971 to 2049 + (-14) =
// 2035. The data transition at 1971 stands after the end of the first window
// and exactly at the beginning of the second, which §31.4.6 excludes, so
// nothing is reported.
//
// What this case claims is that a held transition is discarded and not that
// nothing is ever held: the case above holds one across a closed window and
// reports it against the window that opens next. The 27 between the data
// transition and the second leading reference edge is the start edge offset
// written a second time, which is what stands the transition exactly at the
// beginning rather than near it, and DropTransitionsBefore in
// src/simulator/timing_check_pulse.cpp keeps a held transition only where it
// stands strictly after that beginning.
TEST(DrivenTimingCheckEvaluation,
     NochangeDataAtASecondWindowBeginningReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1904 ctl = 1'b1;\n"
                              "    #32 ctl = 1'b0;\n"
                              "    #35 d = 1'b1;\n"
                              "    #27 ctl = 1'b1;\n"
                              "    #51 ctl = 1'b0;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

}  // namespace
