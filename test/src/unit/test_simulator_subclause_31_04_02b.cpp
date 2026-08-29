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
// dormant at once. That default is what the four cases written before issue
// #3420 are written on, and it is what separates §31.4.2 from §31.4.1's $skew,
// which is event-based and reports nothing when no data event ever comes. The
// four cases written for issue #3420 each write a flag, and each names below
// which of the two it writes.
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
// The two simultaneous cases share a second design, and in both of them the
// reference event and the data event fall at one simulation time. §31.4.2
// decides that case within the timer-based default: "if a data event occurs
// within the limit, then a violation shall not be reported, and the check shall
// become dormant immediately". A data event no time at all after the reference
// event is one that occurs within the limit, so the check ends dormant and
// reports nothing. Both cases claim that, and neither tolerates a report.
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
// The four cases below that were added for issue #3420 are about the two
// optional arguments Table 31-8 gives $timeskew after the notifier:
// `event_based_flag (optional)` and `remain_active_flag (optional)`, each a
// "Constant expression". Issue #3420 is that neither reached the run.
// Parser::ParseTimeskewExtendedArgs in src/parser/parser_specify.cpp parsed
// both into TimingCheckDecl, TimingCheckEntry in
// src/simulator/specify_timing_check.h carried neither, and so every $timeskew
// was evaluated timer-based and every reference event its `&&&` condition
// ruled out was discarded -- which is the remain_active_flag-set behaviour
// applied to every check, whatever the declaration wrote.
//
// TimeskewFlagsAreRegisteredAsWritten is the field-copy half, and it fails
// whatever the driver does with the two fields: it reads them back off the
// check the run registered on SimContext::GetSpecifyManager. It runs two
// designs, one writing both flags and one writing neither, because §31.4.2
// makes the clear pair the default -- "The default behavior for $timeskew is
// timer-based" -- and a build that set every flag would pass the written half
// on its own.
//
// TimeskewSuppressedReferenceEventTurnsTheCheckDormant and
// TimeskewSuppressedReferenceEventWithRemainActiveFlagStillReports are the
// pair for §31.4.2's sentence "This check shall also become dormant if it
// detects a conditioned reference event when its condition is false and the
// remain_active_flag is not set". Their two designs differ in one literal, the
// remain_active_flag written 0 in the first and 11 in the second, and they run
// one stimulus: a first reference edge opens a window and arms the timer, and
// a second reference edge arrives with the conditioning signal `en` at 0 while
// that window is still open. The first case claims the window was closed and
// nothing reported, and the second claims it stood and its timer reported at
// the expiry. One answer given to both would fail one of them.
//
// TimeskewEventBasedFlagReportsOnALateDataEvent is the other flag: "The
// $timeskew check's default timer-based behavior can be altered to event-based
// using the event_based_flag", and event-based "behaves like the $skew check
// when only the event_based_flag is set, except that it becomes dormant after
// reporting the first violation". Its stimulus sends two data events at one
// reference event, the first inside the limit and the second beyond it. That
// is what makes the case fail under a timer-based reading of the same
// declaration: the first data event is one that "occurs within the limit", so
// timer-based turns the check dormant there and reports nothing ever, and only
// the event-based mode is still watching when the second arrives. §31.4.1,
// whose behaviour the flag selects, is what keeps the window open across the
// first -- "after a reference event, the $skew timing check shall never stop
// checking data events for a timing violation".
//
// Those four cases carry limits and times of their own, none of them a limit
// or a time of the two designs above. kFlagDesignBeforeStimulus carries a
// limit of 66 and writes its two flags as 15 and 22 rather than as 1, since
// Table 31-8 makes each a constant expression and any non-zero value sets it,
// so a build comparing the expression against 1 would fail.
// kSuppressedRefDesignBeforeStimulus and kRemainActiveDesignBeforeStimulus
// carry a limit of 74; their `ref_sig` rises at time 915, falls at 932 and
// rises again at 953, and their `tail_sig` rises at 1032, so the expiry of the
// timer a reference event at 915 arms, 915 + 74 = 989, stands after the second
// reference edge and before the trailing transition.
// kEventBasedDesignBeforeStimulus carries a limit of 44; its `ref_sig` rises
// at time 968 and its `data_sig` rises at 986, falls at 1000 and rises again
// at 1025, so the first data event stands 18 time units after the reference
// event and the second stands 57, one inside the limit and one beyond it.
//
// Each of those three designs writes one flag and leaves the other clear, so a
// build that read either flag expression into the other's field would fail one
// of the cases. The swap makes
// TimeskewSuppressedReferenceEventWithRemainActiveFlagStillReports
// event-based, which arms no timer and so reports nothing at 989, and it makes
// TimeskewEventBasedFlagReportsOnALateDataEvent timer-based, which turns the
// check dormant on the data event at 986 and so reports nothing at 1025.
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
// Syntax 31-10 writes `$timeskew ( reference_event , data_event ,
// timing_check_limit [ , [ notifier ] [ , [ event_based_flag ] [ ,
// [ remain_active_flag ] ] ] ] ) ;`, the reference event first and the notifier
// bracketed inside the group the two flags stand in. A declaration writing a
// flag and no notifier therefore writes an empty placeholder where the notifier
// would stand, which is what §31.4.2's own example does: `$timeskew (posedge CP
// &&& MODE, negedge CPN, 50, , event_based_flag, remain_active_flag);`. The
// three flag designs below are written that way. kDesignBeforeStimulus and
// kSimultaneousDesignBeforeStimulus write no flag at all, so each takes
// §31.4.2's default. `ref_sig` is not spelled `ref`, which Table B.1 reserves.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

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

// The design TimeskewFlagsAreRegisteredAsWritten reads the two flags off, up to
// the point the stimulus is spliced in. Its notifier position holds the empty
// placeholder §31.4.2's example writes there, no notifier being declared.
constexpr const char* kFlagDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig, posedge data_sig, 66, , 15, 22);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

// The design TimeskewSuppressedReferenceEventTurnsTheCheckDormant runs, up to
// the point the stimulus is spliced in. §31.7 writes the `&&&` condition on the
// timing_check_event it follows, so `en` gates the reference event alone. The
// remain_active_flag is written 0, which §31.4.2 makes the state its dormancy
// sentence names, and `tail_sig` is there to carry the run past the expiry the
// timer armed at the first reference edge holds.
constexpr const char* kSuppressedRefDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  logic en;\n"
    "  logic tail_sig;\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig &&& en, posedge data_sig, 74, , , 0);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    en = 1'b1;\n"
    "    tail_sig = 1'b0;\n";

// The design TimeskewSuppressedReferenceEventWithRemainActiveFlagStillReports
// runs. It differs from kSuppressedRefDesignBeforeStimulus in the
// remain_active_flag alone, written 11 where that one writes 0, so nothing but
// the flag can explain the two cases answering differently.
constexpr const char* kRemainActiveDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  logic en;\n"
    "  logic tail_sig;\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig &&& en, posedge data_sig, 74, , , 11);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    en = 1'b1;\n"
    "    tail_sig = 1'b0;\n";

// The design TimeskewEventBasedFlagReportsOnALateDataEvent runs. It writes the
// event_based_flag and no remain_active_flag, which is the mode §31.4.2 makes
// "like the $skew check ... except that it becomes dormant after reporting the
// first violation".
constexpr const char* kEventBasedDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig, posedge data_sig, 44, , 37);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

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

// The one timing check the run registered, or nullptr when it registered any
// other number of them. Each design here declares exactly one $timeskew, so a
// case that read a check it did not declare would be reading a check nothing in
// this file put there.
const TimingCheckEntry* OnlyRegisteredCheck(SimFixture& f) {
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  if (mgr == nullptr || mgr->GetTimingChecks().size() != 1) return nullptr;
  return &mgr->GetTimingChecks()[0];
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

// §31.4.2 and Table 31-8: the event_based_flag and the remain_active_flag
// kFlagDesignBeforeStimulus writes, read back off the check the run registered
// on SimContext::GetSpecifyManager, together with the clear pair a declaration
// writing neither registers. The stimulus is empty in both halves because the
// claim is about what the declaration registered, which no transition changes.
//
// The written half alone would pass under a build that set every flag, and the
// default half alone would pass under one that set none. §31.4.2 states the
// default the second half claims: "The default behavior for $timeskew is
// timer-based."
TEST(DrivenTimingCheckEvaluation, TimeskewFlagsAreRegisteredAsWritten) {
  SimFixture flagged;
  ASSERT_TRUE(RanWithStimulus(kFlagDesignBeforeStimulus, "", flagged));
  const TimingCheckEntry* written = OnlyRegisteredCheck(flagged);
  ASSERT_NE(written, nullptr);
  EXPECT_TRUE(written->event_based_flag);
  EXPECT_TRUE(written->remain_active_flag);

  SimFixture bare;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus, "", bare));
  const TimingCheckEntry* defaulted = OnlyRegisteredCheck(bare);
  ASSERT_NE(defaulted, nullptr);
  EXPECT_FALSE(defaulted->event_based_flag);
  EXPECT_FALSE(defaulted->remain_active_flag);
}

// §31.4.2: "This check shall also become dormant if it detects a conditioned
// reference event when its condition is false and the remain_active_flag is not
// set". `ref_sig` rises at time 915 with `en` at 1, which opens the window and
// arms the timer at 915 + 74 = 989. `en` stands at 0 by the time `ref_sig`
// rises again at 953, so that second reference edge is the conditioned event
// the condition ruled out, and it stands 36 time units before the expiry.
// `tail_sig` rises at 1032, which carries the run past 989 whether or not
// anything is left armed to reach it.
//
// The fall of `ref_sig` at 932 is a negedge, which §31.5 makes no occurrence of
// a posedge reference event, so the condition is read at 915 and at 953 and at
// no other moment.
//
// Absence is the claim, as it is in TimeskewSatisfiedInARunReportsNothing
// above, and a null FindDiag is the form for it.
TEST(DrivenTimingCheckEvaluation,
     TimeskewSuppressedReferenceEventTurnsTheCheckDormant) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSuppressedRefDesignBeforeStimulus,
                              "    #915 ref_sig = 1'b1;\n"
                              "    #17 ref_sig = 1'b0;\n"
                              "    en = 1'b0;\n"
                              "    #21 ref_sig = 1'b1;\n"
                              "    #79 tail_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$timeskew violation: data signal"), nullptr);
}

// §31.4.2's dormancy sentence again, with the remain_active_flag set: the
// clause makes the check dormant on a false-conditioned reference event only
// where the flag "is not set", so the window opened at 915 stands and the timer
// it armed reports at 989. This case and
// TimeskewSuppressedReferenceEventTurnsTheCheckDormant above run one stimulus
// against two designs differing in that flag alone, which is what makes the
// two of them say the flag was read rather than one answer handed to both.
//
// The message substring stops before the signal name the report goes on to
// spell, for the reason TimeskewViolationInARunIsReported gives.
TEST(DrivenTimingCheckEvaluation,
     TimeskewSuppressedReferenceEventWithRemainActiveFlagStillReports) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kRemainActiveDesignBeforeStimulus,
                              "    #915 ref_sig = 1'b1;\n"
                              "    #17 ref_sig = 1'b0;\n"
                              "    en = 1'b0;\n"
                              "    #21 ref_sig = 1'b1;\n"
                              "    #79 tail_sig = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$timeskew violation: data signal",
                              LineHolding(kRemainActiveDesignBeforeStimulus,
                                          "$timeskew(posedge ref_sig"),
                              "31.4.2"));
}

// §31.4.2 with the event_based_flag set: `ref_sig` rises at time 968,
// `data_sig` rises at 986 and falls at 1000, and `data_sig` rises again at
// 1025. The first data event stands 986 - 968 = 18 time units after the
// reference event, inside the 44 the limit allows, and the second stands 1025 -
// 968 = 57, beyond it, so (timecheck time) - (timestamp time) > limit holds for
// the second and the violation is reported there.
//
// The first data event is what makes this case fail under the timer-based
// default. §31.4.2 rules that "if a data event occurs within the limit, then a
// violation shall not be reported, and the check shall become dormant
// immediately", so timer-based turns the check dormant at 986 and reports
// nothing at all; event-based keeps the window, §31.4.1 ruling that "after a
// reference event, the $skew timing check shall never stop checking data events
// for a timing violation".
//
// The fall of `data_sig` at 1000 is a negedge, which §31.5 makes no occurrence
// of a posedge data event; it is there so that 1025 is a second rise.
TEST(DrivenTimingCheckEvaluation,
     TimeskewEventBasedFlagReportsOnALateDataEvent) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kEventBasedDesignBeforeStimulus,
                              "    #968 ref_sig = 1'b1;\n"
                              "    #18 data_sig = 1'b1;\n"
                              "    #14 data_sig = 1'b0;\n"
                              "    #25 data_sig = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$timeskew violation: data signal",
      LineHolding(kEventBasedDesignBeforeStimulus, "$timeskew(posedge ref_sig"),
      "31.4.2"));
}

}  // namespace
