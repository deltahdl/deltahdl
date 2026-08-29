// Whether a running design's $setuphold check is evaluated against the stimulus
// that design drives, and what a violation then produces: a report on the
// DiagEngine the run holds.
//
// Every case here writes a design, drives its two signals from an initial
// block, and reads back the diagnostics standing on the fixture. No case builds
// a TimingCheckEntry, and none calls
// SpecifyManager::CheckSetupholdViolation. That is what separates this file
// from test_simulator_subclause_31_03_03a.cpp beside it: every case there hands
// the predicate a reference time, a data time and two limits and asks for the
// verdict, so each proves the verdict is right once something asks and none
// proves that anything asks. Issue #3409 is that nothing did -- every caller of
// that predicate in the tree was a unit test, so no §31.3.3 violation was ever
// reported out of a run.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportTimingViolation in src/simulator/timing_check_driver_internal.h calls
// DiagEngine::Warning; the cases below read it through ReportedWarning rather
// than ReportedError. The report stands on the line the check was written on.
// TimingCheckEntry::loc (src/simulator/specify_timing_check.h) carries that
// position: Parser::ParseTimingCheck (src/parser/parser_specify.cpp) records
// the check's own first token into it, and BuildTimingCheckUnderOptions
// (src/simulator/specify_timing_check.cpp) copies it across. Issue #3414 was
// that the report stood at SourceLoc::None(), whose line is 0, because nothing
// carried that position from the declaration to the run. Each case below names
// the line through LineHolding (lib/cpp/test_helpers/helpers_reported_error.h),
// which reads it off the design text, rather than writing a number down. A
// number goes stale the moment the design gains or loses a line above the
// check.
//
// One $setuphold declaration stands for two constraints. §31.3.3 makes
//
//   $setuphold(posedge clk, d, tSU, tHLD)
//
// equivalent to $setup(d, posedge clk, tSU) with $hold(posedge clk, d, tHLD),
// so a d transition inside tSU before the clk edge violates the setup side and
// one inside tHLD after that edge violates the hold side. The two violating
// cases below drive one side each, which is why they are two cases and not one:
// a driver that checked only one side would report nothing for the case written
// for the other, and both would pass a case that drove both sides at once.
//
// The three cases share one design and differ in their stimulus alone. That is
// what shows a check being run rather than one answer being handed to all
// three: a driver that reported unconditionally would fail the satisfied case,
// and a driver that reported nothing would fail the two violating ones.
//
// The message substring stops before the signal name the report goes on to
// spell, and the two sides of the window share it. What each case claims is
// that a §31.3.3 violation was found for the stimulus it drove, and the
// stimulus is what says which side found it.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, here or in the nine files covering §31.3.4 through §31.4.6 beside this
// one. The limits are 21 (setup) and 6 (hold), neither of them the 0 a
// TimingCheckEntry::limit holds before a limit expression has been evaluated
// into it. The setup-side case leaves 13 time units between the transitions,
// which is inside the 21 the setup side allows and outside the 6 the hold side
// does, so a driver that read the hold limit where the setup limit belongs
// reports nothing and the case fails. The hold-side case leaves 4 and the
// satisfied case 35, and the reference edges stand at times 154, 116 and 163,
// so a case that read its interval, its limit or its edge out of another case's
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
// Syntax 31-5 writes `$setuphold(reference_event, data_event, setup_limit,
// hold_limit, ...)`, the reference event first. §31.3.1's $setup is the one
// check of Clause 31 that writes its data event first, and this is not it.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The design every case here runs, up to the stimulus each case supplies. A
// case hands it to LineHolding, which reads the line the `$setuphold` keyword
// stands on out of this text. The declaration stands above the stimulus, so the
// line it holds here is the line it holds in the whole source.
constexpr const char* kDesignThroughTheCheck =
    "module top;\n"
    "  logic d;\n"
    "  logic clk;\n"
    "  specify\n"
    "    $setuphold(posedge clk, d, 21, 6);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    d = 1'b0;\n"
    "    clk = 1'b0;\n";

// Elaborates, lowers and runs the one design these cases share, with `stimulus`
// as the body of its initial block. False when the source did not elaborate
// cleanly, which a case asserts on before reading anything off the fixture: a
// design rejected before it ran says nothing about §31.3.3 whatever the case
// was written to expect.
bool RanWithStimulus(const std::string& stimulus, SimFixture& f) {
  auto* rtl = ElaborateSrc(std::string(kDesignThroughTheCheck) + stimulus +
                               "  end\n"
                               "endmodule\n",
                           f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

// §31.3.3, setup side: the window ends at the reference edge and opens
// `setup_limit` time units before it. `d` rises at time 141 and `clk` rises at
// time 154, leaving 13 time units against a setup limit of 21.
TEST(DrivenTimingCheckEvaluation, SetupholdSetupSideViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #141 d = 1'b1;\n"
                      "    #13 clk = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setuphold violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$setuphold(posedge clk"), "31.3.3"));
}

// §31.3.3, hold side: the window begins at the reference edge and closes
// `hold_limit` time units after it, running forwards where the setup side's
// runs backwards. `clk` rises at time 116 and `d` rises at time 120, leaving 4
// time units against a hold limit of 6.
TEST(DrivenTimingCheckEvaluation, SetupholdHoldSideViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #116 clk = 1'b1;\n"
                      "    #4 d = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setuphold violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$setuphold(posedge clk"), "31.3.3"));
}

// §31.3.3 again, and the same design: only the stimulus changes. `d` rises at
// time 128 and `clk` rises at time 163, leaving 35 time units of setup against
// a limit of 21, and `d` never transitions after the reference edge, so neither
// side of the window closes with anything inside it.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $setuphold site can make about any design carries this substring
// and there is no other report this case would tolerate.
TEST(DrivenTimingCheckEvaluation, SetupholdSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #128 d = 1'b1;\n"
                      "    #35 clk = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$setuphold violation: data signal"), nullptr);
}

}  // namespace
