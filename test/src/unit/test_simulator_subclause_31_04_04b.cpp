// Whether a running design's $width check is evaluated against the stimulus
// that design drives, what a violation then produces -- a report on the
// DiagEngine the run holds -- and what a declared threshold reaches:
// TimingCheckEntry::threshold on the SpecifyManager the run installed.
//
// Every case here writes a design and elaborates, lowers and runs it. Four of
// them drive the design's one signal from an initial block and read back the
// diagnostics standing on the fixture. Two read the registered check back off
// SimContext::GetSpecifyManager (src/simulator/sim_context.h) through
// SpecifyManager::GetTimingChecks (src/simulator/specify.h) and drive no
// stimulus at all, the check being registered while the design is lowered. No
// case builds a TimingCheckEntry by hand, and none calls
// SpecifyManager::CheckWidthViolation. That is what separates this file from
// test_simulator_subclause_31_04_04a.cpp beside it: every case there hands the
// predicate a reference time, a data time and a limit and asks for the verdict,
// so each proves the verdict is right once something asks and none proves that
// anything asks. Issue #3409 is that nothing did -- every caller of that
// predicate in the tree was a unit test, so no §31.4.4 violation was ever
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
// Each violating case below names that line with LineHolding over the design
// constant it runs rather than writing a number, so the case cannot drift when
// the design gains or loses a line above the $width.
//
// §31.4.4 bounds its window with two edges of ONE signal, which no other driven
// case reaches. Table 31-10 makes the data event implicit -- "the data event
// and the reference event ... are triggered by opposite transitions" -- so a
// posedge reference makes the following negedge the timecheck, and the check
// reports when
//
//   threshold < (timecheck time) - (timestamp time) < limit
//
// §31.3's stability windows and §31.4.1 through §31.4.3's skew checks all
// measure between two named signals, so a driver written for either shape does
// not reach this one.
//
// Each driven pair shares one design and differs in its stimulus alone. That is
// what shows a check being run rather than one answer being handed to both: a
// driver that reported unconditionally would fail each satisfied case, and a
// driver that reported nothing would fail each violating one.
//
// Four cases turn on the threshold that violation condition names. A pulse no
// wider than the threshold is no violation however far it falls below the
// limit, §31.4.4 stating that "the pulse width has to be greater than or equal
// to limit in order to avoid a timing violation, but no violation is reported
// for glitches smaller than the threshold".
// WidthThresholdReachesTheRegisteredEntry claims that the threshold a design
// declares is the value TimingCheckEntry::threshold holds, and reads
// TimingCheckEntry::limit beside it so that one field read in place of the
// other is visible. WidthGlitchBelowTheThresholdReportsNothing and
// WidthPulseAboveTheThresholdIsReported drive one design with a pulse on either
// side of its threshold, so the pair claims the declared value reached the
// verdict and not merely the entry. WidthWithoutAThresholdRegistersZero claims
// the default §31.4.4 states: "The threshold argument shall be included if the
// notifier argument is required. It is permissible to not specify both the
// threshold and notifier arguments, making the default value for the threshold
// zero."
//
// Issue #3418 is that a declared threshold reached neither the entry nor the
// verdict. Parser::ParseTimingCheckTrailingArgs in
// src/parser/parser_specify.cpp appends every trailing operand to
// TimingCheckDecl::limits by position, and BuildTimingCheckUnderOptions in
// src/simulator/specify_timing_check.cpp read limits[1] into
// TimingCheckEntry::limit2 for every kind, so a declared threshold landed in a
// field nothing reads while TimingCheckEntry::threshold stayed 0. Every glitch
// §31.4.4 excludes was therefore reported as a violation.
// WidthWithoutAThresholdRegistersZero reads limit2 for that reason: §31.4.4
// gives $width no second limit, so the field is 0 whatever the design declares.
//
// The message substring stops before the signal name the report goes on to
// spell. What each violating case claims is that the violation was found and
// named as §31.4.4's, and naming a signal in the substring would tie it to
// which field it reached the report through as well.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.3 through §31.4.3, §31.4.5
// and §31.4.6 beside this one. The design that declares a threshold of 0 sets
// its limit to 5, not the 0 a TimingCheckEntry::limit holds before a limit
// expression has been evaluated into it; its violating case holds the pulse for
// 3 time units and its satisfied case for 7, one below the limit and one above,
// and its pulses open at times 806 and 840. The design that declares a non-zero
// threshold sets it to 8 against a limit of 21; its glitch is 6 time units
// wide, below the threshold, its violating pulse is 13, above the threshold and
// below the limit, and its pulses open at times 902 and 934. The design that
// declares no threshold at all sets its limit to 34. All twelve numbers differ,
// so a case that read its interval, its limit, its threshold or its edge out of
// another case's design would compare two numbers that disagree rather than two
// that coincide.
//
// Each driven source drives the signal to a known level before the pulse that
// matters. §31.5 makes posedge the shorthand for edge[01, 0x, x1], so the
// x-to-0 assignment at time 0 is no posedge and opens no window; the negedge it
// does answer to closes no window, there being no timestamp before it.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.
//
// Syntax 31-12 writes `$width(controlled_reference_event, timing_check_limit,
// threshold, notifier)` and names one signal only, the reference event, which
// §31.4.4 requires be an edge specification.

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

// The design the two cases written before issue #3418 run, up to the point the
// stimulus is spliced in. It is a named constant rather than a literal inside
// the call below so that a case can name the line its $width stands on with
// LineHolding (lib/cpp/test_helpers/helpers_reported_error.h). The stimulus
// follows the check, so a line of this text is that line of the whole source.
constexpr const char* kDesignBeforeStimulus =
    "module top;\n"
    "  logic clk;\n"
    "  specify\n"
    "    $width(posedge clk, 5, 0);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clk = 1'b0;\n";

// The design whose $width declares a non-zero threshold, spliced the same way.
// §31.4.4 admits `$width ( negedge clr, lim, thresh, notif );`, so the
// threshold is the third argument of the call and 8 is the value it declares.
constexpr const char* kThresholdDesignBeforeStimulus =
    "module top;\n"
    "  logic clk;\n"
    "  specify\n"
    "    $width(posedge clk, 21, 8);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clk = 1'b0;\n";

// The design whose $width declares no threshold, spliced the same way. §31.4.4
// admits `$width ( negedge clr, lim );`, so the call ends after its limit.
constexpr const char* kNoThresholdDesignBeforeStimulus =
    "module top;\n"
    "  logic clk;\n"
    "  specify\n"
    "    $width(posedge clk, 34);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clk = 1'b0;\n";

// Elaborates, lowers and runs `design` with `stimulus` as the rest of the body
// of its initial block. False when the source did not elaborate cleanly, which
// a case asserts on before reading anything off the fixture: a design rejected
// before it ran says nothing about §31.4.4 whatever the case was written to
// expect.
bool RanWithDesignAndStimulus(const char* design, const std::string& stimulus,
                              SimFixture& f) {
  auto* rtl = ElaborateSrc(std::string(design) + stimulus +
                               "  end\n"
                               "endmodule\n",
                           f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

// The same, for the one design the two cases written before issue #3418 share.
bool RanWithStimulus(const std::string& stimulus, SimFixture& f) {
  return RanWithDesignAndStimulus(kDesignBeforeStimulus, stimulus, f);
}

// The one timing check the run registered, or nullptr when it registered any
// other number of them. Each design here declares exactly one $width, so a
// case that read a check it did not declare would be reading a check nothing
// in this file put there.
const TimingCheckEntry* OnlyRegisteredCheck(SimFixture& f) {
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  if (mgr == nullptr || mgr->GetTimingChecks().size() != 1) return nullptr;
  return &mgr->GetTimingChecks()[0];
}

// §31.4.4: `clk` rises at time 806 and falls at time 809, holding its level for
// 3 time units against a limit of 5.
TEST(DrivenTimingCheckEvaluation, WidthViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #806 clk = 1'b1;\n"
                      "    #3 clk = 1'b0;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$width violation: signal",
      LineHolding(kDesignBeforeStimulus, "$width(posedge clk"), "31.4.4"));
}

// §31.4.4 again, and the same design: only the stimulus changes. `clk` rises at
// time 840 and falls at time 847, holding its level for 7 time units against
// the same limit of 5, which §31.4.4 states as the pulse width being "greater
// than or equal to limit in order to avoid a timing violation".
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $width site can make about any design carries this substring and
// there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, WidthSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #840 clk = 1'b1;\n"
                      "    #7 clk = 1'b0;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$width violation: signal"), nullptr);
}

// §31.4.4: the threshold `$width(posedge clk, 21, 8)` declares is what
// TimingCheckEntry::threshold holds once the design has been lowered, and the
// limit it declares is what TimingCheckEntry::limit holds. The two values
// differ, so a build that read either operand in place of the other fails this
// case. The design drives no pulse, the registration being the whole claim.
TEST(DrivenTimingCheckEvaluation, WidthThresholdReachesTheRegisteredEntry) {
  SimFixture f;
  ASSERT_TRUE(RanWithDesignAndStimulus(kThresholdDesignBeforeStimulus, "", f));
  const TimingCheckEntry* check = OnlyRegisteredCheck(f);
  ASSERT_NE(check, nullptr);
  EXPECT_EQ(check->limit, 21u);
  EXPECT_EQ(check->threshold, 8u);
}

// §31.4.4: `clk` rises at time 902 and falls at time 908, holding its level for
// 6 time units against a threshold of 8. The clause reports a violation for
// "threshold < (timecheck time) - (timestamp time) < limit", and 6 is not
// greater than 8, so the pulse is one of the "glitches smaller than the
// threshold" the clause excludes even though it is far below the limit of 21.
TEST(DrivenTimingCheckEvaluation, WidthGlitchBelowTheThresholdReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithDesignAndStimulus(kThresholdDesignBeforeStimulus,
                                       "    #902 clk = 1'b1;\n"
                                       "    #6 clk = 1'b0;\n",
                                       f));
  EXPECT_EQ(FindDiag(f, "$width violation: signal"), nullptr);
}

// §31.4.4 again, and the same design: only the stimulus changes. `clk` rises at
// time 934 and falls at time 947, holding its level for 13 time units, which is
// greater than the threshold of 8 and less than the limit of 21. That is the
// clause's violation condition met on both sides.
TEST(DrivenTimingCheckEvaluation, WidthPulseAboveTheThresholdIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithDesignAndStimulus(kThresholdDesignBeforeStimulus,
                                       "    #934 clk = 1'b1;\n"
                                       "    #13 clk = 1'b0;\n",
                                       f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$width violation: signal",
      LineHolding(kThresholdDesignBeforeStimulus, "$width(posedge clk"),
      "31.4.4"));
}

// §31.4.4: `$width(posedge clk, 34)` declares no threshold, and the clause
// makes "the default value for the threshold zero", so
// TimingCheckEntry::threshold is 0. TimingCheckEntry::limit2 is 0 as well,
// §31.4.4 giving $width no second limit for a build to write one into. The
// limit is read beside them because it is the one non-zero value the
// declaration carries, so a case reading an entry no declaration reached would
// fail on it. The design drives no pulse, the registration being the whole
// claim.
TEST(DrivenTimingCheckEvaluation, WidthWithoutAThresholdRegistersZero) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithDesignAndStimulus(kNoThresholdDesignBeforeStimulus, "", f));
  const TimingCheckEntry* check = OnlyRegisteredCheck(f);
  ASSERT_NE(check, nullptr);
  EXPECT_EQ(check->limit, 34u);
  EXPECT_EQ(check->threshold, 0u);
  EXPECT_EQ(check->limit2, 0u);
}

}  // namespace
