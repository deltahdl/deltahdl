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
// the start edge offset and -14 as the end edge offset, and the three cases
// over it are what cover the offsets: NochangeOffsetsAreRegisteredAsWritten
// reads both back off the registered TimingCheckEntry, and the two cases after
// it place a data transition where the offsets decide the verdict.
//
// Issue #3418 is why those three were not here before. A declared offset never
// reached the registered check: BuildTimingCheckUnderOptions in
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
// transition, both at that one time. A transition standing strictly before the
// leading reference edge would be dropped instead of measured,
// RecordNochangeData in src/simulator/timing_check_pulse.cpp returning without
// recording anything while no leading edge has been seen. A transition at the
// leading edge time still turns on the start edge offset, §31.4.6 excluding the
// end points: at offset 0 the beginning of the window is the data event time
// and the check is satisfied, and at offset 27 the beginning stands 27 earlier
// and the same transition is inside.
//
// NochangeViolationInARunIsReported and NochangeSatisfiedInARunReportsNothing
// share kDesignBeforeStimulus and differ in their stimulus alone, and
// NochangeStartEdgeOffsetWidensTheWindowIntoAViolation and
// NochangeDataOutsideTheWidenedWindowReportsNothing stand in that same relation
// over kOffsetDesignBeforeStimulus. That is what shows a check being run rather
// than one answer being handed to both: a driver that reported unconditionally
// would fail the satisfied case, and a driver that reported nothing would fail
// the violating one.
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
// The two edge offsets are 27 and -14. They differ from each other, they differ
// in sign, and neither is any interval or any edge time a case writes, so a
// build that read one of them where the other was written, or read either into
// TimingCheckEntry::limit, answers with a number that disagrees. The one
// interval written as 0 is the one between the leading reference edge and the
// data transition of
// NochangeStartEdgeOffsetWidensTheWindowIntoAViolation, where the coincidence
// is what the case is about.
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

}  // namespace
