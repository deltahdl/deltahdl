// Whether a running design's $fullskew check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Every case here writes a design, drives its two signals from an initial
// block, and reads back the diagnostics standing on the fixture. No case builds
// a TimingCheckEntry, and none calls SpecifyManager::CheckFullskewViolation,
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
// with limit set to limit1 when the reference transitions first. The first two
// cases below move the reference first, so limit1 is the one that decides them.
//
// The first two cases share one design and differ in their stimulus alone. That
// is what shows a check being run rather than one answer being handed to both:
// a driver that reported unconditionally would fail the satisfied case, and a
// driver that reported nothing would fail the violating one.
//
// The third and fourth cases share a second design, and in both of them the
// reference event and the data event fall at one simulation time. §31.4.3
// settles that outright: "Simultaneous transitions on the reference and data
// signals shall not cause $fullskew to report a timing violation, even when the
// skew limit value is zero." Each of the two asserts that nothing was reported,
// and the two differ in the order their two assignments are written in and in
// nothing else, so together they claim the verdict does not follow that order.
//
// Neither of those two cases fails today, and neither is regression coverage
// for issue #3421. $fullskew is the one of §31.4's three skew checks that is
// symmetric in its two events. OnFullskewEvent
// (src/simulator/timing_check_skew.cpp) makes whichever event arrives while a
// window opened by the other signal is open the timecheck event, and §31.4.3
// rules that such an event, "occurring within the time limit after a preceding
// timestamp event", "turns the timing check dormant". Both commit orders
// therefore reached a dormant check before the change issue #3421 asks for, and
// both reach one after it. What the two cases guard is that the arming shape
// that change introduces keeps $fullskew symmetric: each watcher records that
// its event happened and asks for one deferred pass, ApplySlotEvents in that
// same file applies the reference event before the data event once the slot's
// active and reactive region sets are drained, and
// ScheduleTimingCheckEvaluation (src/simulator/timing_check_driver_internal.h)
// is what defers that pass to Region::kPrePostponed. The $hold pair in
// test_simulator_subclause_31_03_01b.cpp is what catches the defect issue #3421
// names, $hold being evaluated at one of its two events alone.
//
// Each of those two cases writes its two assignments as two statements of one
// initial block with no delay between them. That is what makes the order the
// two signals commit in explicit and deterministic. A pair of continuous
// assignments would leave that order to the order the two were lowered in.
//
// Each of those two cases then holds time open past the point a timer left
// armed would have fired. ArmTimeout (src/simulator/timing_check_skew.cpp)
// schedules the timer-based report at the timestamp time plus the limit the
// window was opened against, so a run that ended at the two transitions would
// say nothing about a window left open. The trailing `#91` carries each of the
// two runs to time 869, past the 836 a timer measured against limit1 would fire
// at and past the 861 one measured against limit2 would.
//
// The message substring stops before the signal names the report goes on to
// spell. §31.4.3's message names both signals and neither is "the data signal",
// the roles being decided by transition order rather than by argument position,
// so the substring here is the one the report opens with and nothing more.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.4.2 and §31.4.4
// through §31.4.6 beside this one. The first design's limits are 29 (limit1)
// and 64 (limit2), neither of them the 0 a TimingCheckEntry::limit holds before
// a limit expression has been evaluated into it. The violating case leaves 49
// time units between the transitions, which is outside the 29 limit1 allows and
// inside the 64 limit2 allows, so a driver that read limit2 where limit1
// belongs reports nothing and the case fails. The satisfied case leaves 26, and
// the reference edges stand at times 703 and 740, so a case that read its
// interval, its limit or its edge out of another case's design would compare
// two numbers that disagree rather than two that coincide.
//
// The two simultaneous cases run a second design, whose limits are 58 (limit1)
// and 83 (limit2) and whose two transitions both stand at time 778. None of
// those three numbers is a limit, an interval or a time the first two cases
// use, so a case that read a limit or an edge out of the other design would
// again compare two numbers that disagree. The two limits differ from each
// other, so the deadline a window opened by the reference signal is measured
// against differs from the one a window opened by the data signal is measured
// against: WindowLimit (src/simulator/timing_check_skew.cpp) returns
// TimingCheckEntry::limit for the first and TimingCheckEntry::limit2 for the
// second. Neither limit is 0, because at a limit of zero the moment a timer
// would fire and the moment the two signals move are one number, and a case
// built on that cannot tell a cancelled timer from one that had nowhere later
// to fire. The trailing delay is 91, which is longer than either limit and is
// used nowhere else here.
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
// timing_check_limit, timing_check_limit [, [notifier] [, [event_based_flag]
// [, [remain_active_flag]]]])`, the reference event first and limit1 before
// limit2. The three optional arguments nest, so a declaration that writes one
// of them writes an empty placeholder for each argument before it, and
// Parser::ParseTimeskewExtendedArgs (src/parser/parser_specify.cpp) reads a
// placeholder as a comma with nothing consumed for it. That is why the
// remain_active_flag case below writes `, , , 1` after limit2 and the
// event_based_flag cases write `, , 1`. Table 31-9 lists both flags as
// Constant expressions, and BuildTimingCheckUnderOptions
// (src/simulator/specify_timing_check.cpp) sets each on any non-zero value.
//
// The first four cases write no flag, so each of those declarations takes
// §31.4.3's timer-based default; the violating case drives its data edge after
// the elapse rather than omitting it, so it reports under that default and
// under the event-based reading alike, and the two simultaneous cases report
// nothing under either, the event-based reading arming no timer and the
// timer-based reading having its timer cancelled by the timecheck event.
// `ref_sig` is not spelled `ref`, which Table B.1 reserves.
//
// The last four cases are the two flags, and issue #3420 is that neither
// reached the run: TimingCheckDecl carried an event_based_flag and a
// remain_active_flag that Parser::ParseTimeskewExtendedArgs had parsed,
// TimingCheckEntry (src/simulator/specify_timing_check.h) carried neither, and
// so every $fullskew was evaluated as timer-based and every reference event
// whose `&&&` condition was false was discarded. Discarding it is the
// remain_active_flag-set behaviour, applied to every check whatever its
// declaration wrote.
//
// The first two of them are §31.4.3's rule for a suppressed reference event,
// which the clause states for $fullskew in its own words: "unless the second
// timestamp event has an associated condition whose value is false. In such a
// case, the behavior of $fullskew depends on the remain_active_flag. If the
// flag is set, then the second timestamp event is simply ignored. If the flag
// is not set and if the timing check is active, then the timing check turns
// dormant." §31.4.2 states the same rule for $timeskew separately, so a fix
// keyed to TimingCheckKind::kTimeskew alone would leave both of these cases
// failing.
//
// Those two share one stimulus and one set of literals and differ in the
// declaration alone, one writing no flag and the other writing
// remain_active_flag. A driver that ignored the flag would fail one of the two
// whichever way it read a suppressed reference event. Their design gives its
// reference event the `&&& en` condition §31.7 writes, with `en` held at 0 for
// the whole run, so every reference edge is suppressed and only `data_sig` can
// open a window. §31.4.3 admits that outright, its two events being symmetric:
// "The data event is the timestamp event, and the reference event is the
// timecheck event when the data event precedes the reference event." A window
// opened by the data signal is measured against limit2, WindowLimit
// (src/simulator/timing_check_skew.cpp) returning TimingCheckEntry::limit2 for
// it.
//
// Their limits are 31 (limit1) and 47 (limit2), `data_sig` rises at time 214
// and `ref_sig` at time 255, and the run then stands open to time 317. The
// window opens at 214 and ArmTimeout (src/simulator/timing_check_skew.cpp)
// schedules its report at 214 + 47 = 261. The suppressed reference edge at 255
// falls inside that window and past the 214 + 31 = 245 a timer measured against
// limit1 would fire at, so a driver that read limit1 where limit2 belongs
// reports in the case that expects silence and that case fails. Nothing else
// moves after 255, so the flag decides the whole outcome: clear, the window
// closes at 255 and the timer with it; set, the event is ignored and the timer
// fires at 261.
//
// The last two cases are §31.4.3's event_based_flag: "In this mode, $fullskew
// is similar to $skew in that a violation is reported not upon elapse of the
// time limit after the timestamp event (as in timer-based mode), but rather if
// a timecheck event occurs after the time limit. Such an event ends the first
// timing window and immediately begins a new timing window, where it acts as
// the timestamp event of the new window. A timecheck event within the time
// limit ends the timing window and turns the timing check dormant, and no
// violation is reported."
//
// They share one design, whose limits are 73 (limit1) and 96 (limit2) and whose
// `ref_sig` rises at time 412, and differ in when `data_sig` rises. The
// reference signal opens the window, so limit1 is what the timecheck event is
// measured against. The reporting case puts `data_sig` at 500, which is 88 time
// units after the timestamp and so beyond the 73 limit1 allows and inside the
// 96 limit2 allows: a driver that read limit2 where limit1 belongs finds 88
// within the limit and reports nothing, and the case fails. The silent case
// puts `data_sig` at 467, 55 time units after the timestamp and inside limit1.
// Both then stand open to time 511 or later, past the 412 + 73 = 485 a timer
// measured against limit1 would fire at and past the 412 + 96 = 508 one
// measured against limit2 would.
//
// Neither of those two states that the window continued after the report, and
// the last case of the file is what does. §31.4.3's event-based sentence does
// not stop at reporting: such a timecheck event "ends the first timing window
// and immediately begins a new timing window, where it acts as the timestamp
// event of the new window". Nothing in a single report shows that, so the case
// drives two timecheck events, each beyond the limit measured from the
// timestamp the one before it became, and asserts that both were reported. An
// implementation that closed the window after reporting makes one report and
// the case fails, and that is the live mistake: OnTimeskewDataEvent
// (src/simulator/timing_check_skew.cpp) closes the window after an event-based
// report where §31.4.2 gives $timeskew a clear remain_active_flag, and
// §31.4.3's event-based mode continues the check whatever its
// remain_active_flag says.
//
// The number of reports is the claim there, where CLAUDE.md otherwise has a
// case name the rule a report enforces rather than count reports. The rule
// §31.4.3 states is that the window continues, and a run in which it does not
// continue reports a strict subset of what a run in which it does reports, so
// the second report is the only observable the rule has. The case still names
// the rule: ReportedWarning answers the message, the line and the subclause of
// the first report, and FindDiagFrom
// (lib/cpp/test_fixtures/fixture_simulator.h) started one past that report's
// position is what asks for the second.
//
// None of the three event_based_flag cases tells the event-based mechanism from
// the timer-based one by what was reported, and none can. A timecheck event
// beyond the limit is one the timer-based deadline has already elapsed under,
// so every event-based report has a timer-based report standing for the same
// window, and a run that dropped the flag reports at least as often as one that
// read it -- three times over the last case's stimulus, against the two the fix
// makes. What fails a run carrying neither flag is
// FullskewSuppressedRefEventWithoutRemainActiveFlagTurnsCheckDormant and
// FullskewSuppressedRefEventWithRemainActiveFlagLeavesTimerStanding above,
// which differ in the declaration alone.
//
// The last case's design is the event_based_flag design, so its limits are the
// 73 and the 96 the two cases before it use. `ref_sig` rises at time 130 and is
// the timestamp, and `data_sig` rises at time 209, 79 time units later: beyond
// the 73 limit1 allows and inside the 96 limit2 allows, so a driver that read
// limit2 where limit1 belongs reports nothing and the case fails. That report
// makes `data_sig` the timestamp of a window opened at 209, which WindowLimit
// measures against limit2. `ref_sig` falls at time 221 and rises again at time
// 327, 118 time units after 209 and so beyond that 96, and the run then stands
// open to time 364. The fall is not a posedge -- §31.5 makes posedge every
// transition that leaves 0 or arrives at 1 -- so it is no occurrence of the
// check, and it is what lets `ref_sig` produce a second posedge at all.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The design the first two cases run, up to the point the stimulus is spliced
// in. It is a named constant rather than a literal inside the call below so
// that a case can name the line its $fullskew stands on with LineHolding
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

// The design the two simultaneous cases run, up to the point their stimulus is
// spliced in. It differs from kDesignBeforeStimulus in its two limits alone.
constexpr const char* kSimultaneousDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig, posedge data_sig, 58, 83);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

// The design the suppressed-reference-event case with no flag runs, up to the
// point kSuppressedRefStimulus is spliced in. §31.7 writes the condition as
// `&&& en` on the timing_check_event it gates, and `en` is a variable of the
// same module because §31.7 has the conditioning signal named by the declaring
// module's own name.
constexpr const char* kSuppressedRefDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  logic en;\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig &&& en, posedge data_sig, 31, 47);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    en = 1'b0;\n";

// The same design with Syntax 31-11's remain_active_flag written as 1. It
// differs from kSuppressedRefDesignBeforeStimulus in the three arguments after
// limit2 and in nothing else: an empty notifier, an empty event_based_flag and
// the flag itself.
constexpr const char* kRemainActiveDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  logic en;\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig &&& en, posedge data_sig, 31, 47, , , 1);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    en = 1'b0;\n";

// The stimulus both suppressed-reference-event cases run, so that the two of
// them differ in their declaration alone. `data_sig` rises at time 214 and
// opens a window measured against the 47 limit2 allows, `ref_sig` rises at time
// 255 with `en` at 0, and the run stands open to time 317, past the 261 the
// window's timer is due at.
constexpr const char* kSuppressedRefStimulus =
    "    #214 data_sig = 1'b1;\n"
    "    #41 ref_sig = 1'b1;\n"
    "    #62;\n";

// The design both event_based_flag cases run, up to the point their stimulus is
// spliced in. Syntax 31-11 puts the event_based_flag after the notifier, so the
// empty argument between limit2 and the 1 is the notifier §31.6 makes optional.
constexpr const char* kEventBasedDesignBeforeStimulus =
    "module top;\n"
    "  logic ref_sig;\n"
    "  logic data_sig;\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig, posedge data_sig, 73, 96, , 1);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

// Elaborates, lowers and runs `design` with `stimulus` as the rest of the body
// of its initial block. False when the source did not elaborate cleanly, which
// a case asserts on before reading anything off the fixture: a design rejected
// before it ran says nothing about §31.4.3 whatever the case was written to
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

// The position in `f`'s diagnostics of the first whose message contains
// `needle`, or the number of diagnostics when none does. The case below that
// claims two reports passes this position plus one to FindDiagFrom, so what it
// asks for is a report beyond the one it already named rather than a report
// beyond a position it guessed.
std::size_t PositionOfFirstDiag(const SimFixture& f, std::string_view needle) {
  const auto& diags = f.diag.Diagnostics();
  for (std::size_t i = 0; i < diags.size(); ++i) {
    if (diags[i].message.find(needle) != std::string::npos) return i;
  }
  return diags.size();
}

// §31.4.3: `ref_sig` rises at time 703 and `data_sig` rises at time 752, so the
// two signals move 49 time units apart against the 29 limit1 allows the data
// signal to trail the reference by.
TEST(DrivenTimingCheckEvaluation, FullskewViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #703 ref_sig = 1'b1;\n"
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
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #740 ref_sig = 1'b1;\n"
                              "    #26 data_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

// §31.4.3: "Simultaneous transitions on the reference and data signals shall
// not cause $fullskew to report a timing violation, even when the skew limit
// value is zero." `ref_sig` and `data_sig` both rise at time 778, the reference
// signal being assigned first, and the run then stands open to time 869, past
// the 836 a timer measured against the 58 limit1 would fire at and past the 861
// one measured against the 83 limit2 would.
//
// Absence is the claim here as it is in
// FullskewSatisfiedInARunReportsNothing above, and it is asserted the same way
// and for the same reason.
TEST(DrivenTimingCheckEvaluation,
     FullskewSimultaneousEventsWithReferenceAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #778 ref_sig = 1'b1;\n"
                              "    data_sig = 1'b1;\n"
                              "    #91;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

// §31.4.3's simultaneous sentence again, with the data signal `data_sig`
// assigned first. This case and
// FullskewSimultaneousEventsWithReferenceAssignedFirstReportNothing above
// differ in the order of two assignments at one simulation time and in nothing
// else, which is what makes the two of them say that $fullskew answers a
// simultaneous pair the same way whichever of its two signals commits first.
TEST(DrivenTimingCheckEvaluation,
     FullskewSimultaneousEventsWithDataAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #778 data_sig = 1'b1;\n"
                              "    ref_sig = 1'b1;\n"
                              "    #91;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

// §31.4.3: "If the flag is not set and if the timing check is active, then the
// timing check turns dormant." `data_sig` rises at time 214 and opens a window
// measured against the 47 limit2 allows, so its timer is due at 261. `ref_sig`
// rises at time 255 with `en` at 0, which §31.7 makes no occurrence of the
// check, and the remain_active_flag is not written, so the window closes at 255
// and the timer is cancelled. The run then stands open to time 317, past the
// 261 the timer was due at and past the 245 a timer measured against the 31
// limit1 would have been due at.
//
// §31.4.2 states this rule for $timeskew in a sentence of its own, so a fix
// keyed to TimingCheckKind::kTimeskew alone leaves this case failing.
//
// Absence is the claim, and ReportedWarning cannot state it, for the reason
// FullskewSatisfiedInARunReportsNothing above gives. The acceptance form is a
// null FindDiag.
TEST(DrivenTimingCheckEvaluation,
     FullskewSuppressedRefEventWithoutRemainActiveFlagTurnsCheckDormant) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSuppressedRefDesignBeforeStimulus,
                              kSuppressedRefStimulus, f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

// §31.4.3: "If the flag is set, then the second timestamp event is simply
// ignored." This case runs the stimulus
// FullskewSuppressedRefEventWithoutRemainActiveFlagTurnsCheckDormant above runs
// and changes the declaration alone, writing Syntax 31-11's remain_active_flag
// as 1. The suppressed reference edge at time 255 therefore leaves the window
// `data_sig` opened at 214 standing, its timer still due at 214 + 47 = 261, and
// the timer reports there because no timecheck event ever arrives -- every
// reference edge of this design is one `en` ruled out.
TEST(DrivenTimingCheckEvaluation,
     FullskewSuppressedRefEventWithRemainActiveFlagLeavesTimerStanding) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kRemainActiveDesignBeforeStimulus,
                              kSuppressedRefStimulus, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$fullskew violation: signals",
                              LineHolding(kRemainActiveDesignBeforeStimulus,
                                          "$fullskew(posedge ref_sig &&& en"),
                              "31.4.3"));
}

// §31.4.3, event-based: "a violation is reported ... if a timecheck event
// occurs after the time limit." `ref_sig` rises at time 412 and is the
// timestamp event, so the window is measured against the 73 limit1 allows.
// `data_sig` rises at time 500, 88 time units later and so beyond that limit
// and inside the 96 limit2 allows, and it is the timecheck event of that
// window. The run then stands open to time 544.
//
// The event_based_flag arms no timer, so the report this case reads back can
// only have come from the timecheck event. What it claims is that the
// event-based detection exists, not that the flag reached the run: a driver
// that ignored the flag would report here off a timer due at 412 + 73 = 485.
// FullskewSuppressedRefEventWithoutRemainActiveFlagTurnsCheckDormant and
// FullskewSuppressedRefEventWithRemainActiveFlagLeavesTimerStanding above are
// what fail a run that sets no flag.
TEST(DrivenTimingCheckEvaluation,
     FullskewEventBasedTimecheckBeyondLimitIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kEventBasedDesignBeforeStimulus,
                              "    #412 ref_sig = 1'b1;\n"
                              "    #88 data_sig = 1'b1;\n"
                              "    #44;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$fullskew violation: signals",
      LineHolding(kEventBasedDesignBeforeStimulus, "$fullskew(posedge ref_sig"),
      "31.4.3"));
}

// §31.4.3, event-based: "A timecheck event within the time limit ends the
// timing window and turns the timing check dormant, and no violation is
// reported." This case runs the design
// FullskewEventBasedTimecheckBeyondLimitIsReported above runs and moves its
// data edge alone. `ref_sig` rises at time 412 and `data_sig` at time 467, 55
// time units later and so inside the 73 limit1 allows, and the run then stands
// open to time 511 -- past the 485 a timer measured against limit1 would have
// been due at and past the 508 one measured against limit2 would.
//
// Absence is the claim, and it is asserted through a null FindDiag for the
// reason FullskewSatisfiedInARunReportsNothing above gives.
TEST(DrivenTimingCheckEvaluation,
     FullskewEventBasedTimecheckWithinLimitReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kEventBasedDesignBeforeStimulus,
                              "    #412 ref_sig = 1'b1;\n"
                              "    #55 data_sig = 1'b1;\n"
                              "    #44;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

// §31.4.3, event-based: such a timecheck event "ends the first timing window
// and immediately begins a new timing window, where it acts as the timestamp
// event of the new window". Two timecheck events run here, each beyond the
// limit measured from the timestamp the one before it became, and both are
// reported.
//
// `ref_sig` rises at time 130 and opens a window measured against the 73 limit1
// allows, the reference signal being the timestamp. `data_sig` rises at time
// 209, 79 time units later and so beyond that limit, and is reported; it then
// becomes the timestamp of a window opened at 209, which WindowLimit
// (src/simulator/timing_check_skew.cpp) measures against the 96 limit2 allows.
// `ref_sig` falls at time 221, which §31.5 makes no posedge and so no
// occurrence of the check, and rises again at time 327, 118 time units after
// 209 and so beyond that 96, and is reported. The run then stands open to time
// 364.
//
// The second report is the whole claim, and counting is what states it: §31.4.3
// rules that the window continues, and a run that turned the check dormant on
// the first violation -- §31.4.2's rule for a $timeskew with a clear
// remain_active_flag, which OnTimeskewDataEvent in that same file applies --
// reports at 209 and stays silent at 327. ReportedWarning names the message,
// the line and the subclause of the first report, and FindDiagFrom
// (lib/cpp/test_fixtures/fixture_simulator.h) started one past that report's
// position is what asks for the second, so a run that reported nothing at all
// fails the first half rather than passing the second.
TEST(DrivenTimingCheckEvaluation,
     FullskewEventBasedTimecheckBecomesTimestampOfANewWindow) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kEventBasedDesignBeforeStimulus,
                              "    #130 ref_sig = 1'b1;\n"
                              "    #79 data_sig = 1'b1;\n"
                              "    #12 ref_sig = 1'b0;\n"
                              "    #106 ref_sig = 1'b1;\n"
                              "    #37;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$fullskew violation: signals",
      LineHolding(kEventBasedDesignBeforeStimulus, "$fullskew(posedge ref_sig"),
      "31.4.3"));
  std::size_t first = PositionOfFirstDiag(f, "$fullskew violation: signals");
  EXPECT_NE(FindDiagFrom(f, first + 1, "$fullskew violation: signals"),
            nullptr);
}

}  // namespace
