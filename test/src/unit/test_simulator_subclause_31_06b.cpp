// §31.6's Table 31-13 reached through a running design: what a timing violation
// does to the notifier variable the violated check names, read back off that
// variable once the run has finished. Every case below writes a module, drives
// its two timing check signals from an initial block, and reads the notifier
// out of the SimContext the run left behind.
//
// No case here calls ToggleNotifierOnViolation
// (src/simulator/specify_timing_violation.cpp) or
// SpecifyManager::CheckSetupViolation. That is what separates this file from
// test_simulator_subclause_31_06a.cpp beside it: every case there hands one of
// those two functions a value directly and none drives a design, so each proves
// Table 31-13 is answered once something asks and none proves that a run asks.
//
// Issue #3413 is the defect these cases cover. ToggleNotifierOnViolation
// answered x for a notifier holding x and 0 for a notifier holding z, which
// inverts Table 31-13's fourth row and breaks its first. The two rows now
// answer z for z and 1 for x.
//
// Table 31-13 states the whole of what a violation does to a notifier. Its
// BEFORE and AFTER columns are x and "Either 0 or 1", 0 and 1, 1 and 0, and z
// and z. §31.6 says of the variable itself that "the notifier is a variable,
// declared in the module where timing check tasks are invoked, that is passed
// as the last argument to a system timing check", and that "whenever a timing
// violation occurs, the timing check updates the value of the notifier". The
// clause gives the notifier its purpose in the same terms: "timing check
// notifiers detect timing check violations behaviorally and, therefore, take an
// action as soon as a violation occurs. Such notifiers can be used to print an
// informative error message describing the violation or to propagate an x value
// at the output of the device that reported the violation." A design reading
// its own notifier is what those two uses need, so the value the run leaves in
// the variable is what each case below asserts.
//
// Each case reads the notifier's least significant bit through
// Logic4Vec::words[0].aval and Logic4Vec::words[0].bval rather than through
// Logic4Vec::ToUint64. The claim is about a four-state value, and
// common/types.h records that ToUint64 collapses x into z, so a case reading it
// could not tell Table 31-13's first row from its fourth. The encoding is
// (aval, bval): 0 is (0, 0), 1 is (1, 0), x is (1, 1) and z is (0, 1). Only bit
// 0 is read, because ToggleNotifier in
// src/simulator/timing_check_driver_internal.h writes bit 0 and leaves the rest
// of the variable as it stands.
//
// The x case asserts what the answer is not. Table 31-13's first row reads
// "Either 0 or 1", which grants a licence rather than naming a value, so the
// case asserts that the bval bit is clear -- that the notifier holds neither x
// nor z -- and asserts nothing about which of the two known values it holds.
// Pinning the 1 the implementation returns today would assert the choice §31.6
// leaves open.
//
// Four cases expect a toggle and each of the four drives its $setup window into
// a violation. The fifth satisfies its window, and without it a run that
// toggled the notifier on every reference edge would pass the 0-to-1 and
// 1-to-0 cases: §31.6 updates the notifier when a violation occurs and at no
// other time.
//
// Each of the four violating cases also asserts that the violation was
// reported, through ReportedWarning. Without that assertion a run that never
// evaluated the check at all would pass the z case, which expects the notifier
// left where it started. The fifth case asserts the absence of that report with
// a null FindDiag, absence being a claim ReportedWarning cannot state.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportViolation in src/simulator/timing_check_driver.cpp calls
// DiagEngine::Warning under §31.3.1. The report stands on the line the check
// was written on. TimingCheckEntry::loc in
// src/simulator/specify_timing_check.h carries that line, and
// Parser::ParseTimingCheck in src/parser/parser_specify.cpp sets it to the
// location of the check's own first token. Each case below names the line
// through LineHolding in lib/cpp/test_helpers/helpers_reported_error.h rather
// than writing a number, so no case drifts when its design gains or loses a
// line. Issue #3414 is the defect that left the line 0: nothing carried the
// position from the declaration to the run, so the report stood at
// SourceLoc::None().
//
// The literals are picked so that no two quantities a case tells apart share a
// value. The limits are 37, 41, 43, 47 and 29, one per case and none of them
// the 0 a TimingCheckEntry::limit holds before a limit expression has been
// evaluated into it. The data transitions stand at times 101, 107, 109, 113 and
// 127 and the reference edges at 114, 124, 128, 136 and 158, ten distinct
// times; the intervals they leave are 13, 17, 19, 23 and 31, five more values
// distinct from each other, from every limit and from every time. So a case
// that read its interval, its limit or its edge out of another case's design
// would compare two numbers that disagree rather than two that happen to
// coincide.
//
// Each source drives `d` and `clk` to a known level before the transitions its
// case counts. §31.5 makes posedge the shorthand for edge[01, 0x, x1], so the
// x-to-0 assignment to `clk` at time 0 is no posedge and opens no window, and
// each case's timeline begins at its first delay.
//
// The notifier is the one signal not driven to a known level first, because its
// value before the violation is what each case is about. Each source assigns it
// in the same initial block, ahead of every delay, so the value under test
// stands in the variable before the reference edge arrives. That assignment
// provokes nothing: `setup_notifier` is neither the data_event's signal nor the
// reference_event's, so ArmStabilityWindow in
// src/simulator/timing_check_driver.cpp arms no watcher on it, and writing it
// opens no window and evaluates no check.
//
// Syntax 31-3 writes `$setup(data_event, reference_event, timing_check_limit,
// notifier)`. The notifier is the last argument, and $setup is the one check of
// Clause 31 whose first argument is the data event.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The part of a §31.3.1 report that names the rule without naming a signal.
// ReportViolation in src/simulator/timing_check_driver.cpp goes on to spell the
// two signals the check measures between, and a case naming one of them in the
// substring would tie its claim to which field each reached the report through
// as well.
constexpr std::string_view kSetupViolation = "$setup violation: data signal";

// The design every case below drives, differing in the four values the cases
// are told apart by: `initial_value` is the notifier's value before the
// violation, which is Table 31-13's BEFORE column; `limit` is the $setup's
// timing_check_limit; `data_time` is when `d` rises; and `interval` is how long
// after that `clk` rises, which is the setup time the limit is compared
// against.
//
// One design serves all five because §31.6 states one rule over the notifier
// whatever the value it held. What a case varies is that value and whether the
// window was violated, so a second design shape would vary something no case
// asks about.
std::string NotifierDesign(std::string_view initial_value, unsigned limit,
                           unsigned data_time, unsigned interval) {
  return std::string(
             "module top;\n"
             "  logic d;\n"
             "  logic clk;\n"
             "  logic setup_notifier;\n"
             "  specify\n"
             "    $setup(d, posedge clk, ") +
         std::to_string(limit) +
         ", setup_notifier);\n"
         "  endspecify\n"
         "  initial begin\n"
         "    setup_notifier = " +
         std::string(initial_value) +
         ";\n"
         "    d = 1'b0;\n"
         "    clk = 1'b0;\n"
         "    #" +
         std::to_string(data_time) + " d = 1'b1;\n    #" +
         std::to_string(interval) +
         " clk = 1'b1;\n"
         "  end\n"
         "endmodule\n";
}

// Table 31-13's fourth row: BEFORE z, AFTER z. `d` rises at time 101 and `clk`
// rises at time 114, leaving 13 time units of setup against a limit of 37,
// which §31.3.1 makes a violation. The notifier holds z when that violation is
// found and holds z afterwards.
//
// The case asserts both halves of the encoding rather than asking whether the
// value is unknown, because z is (aval 0, bval 1) and x is (aval 1, bval 1): a
// notifier left holding x would satisfy a claim that only said the value is not
// known. This is the row issue #3413 inverted, ToggleNotifierOnViolation having
// answered 0 for a notifier holding z.
TEST(NotifierUpdateDriven, ZNotifierSurvivesADrivenViolation) {
  SimFixture f;
  const std::string kDesign = NotifierDesign("1'bz", 37, 101, 13);
  auto* notifier = RunAndFindVar(kDesign, f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  EXPECT_EQ(notifier->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 1u);
}

// Table 31-13's first row: BEFORE x, AFTER "Either 0 or 1". `d` rises at time
// 107 and `clk` rises at time 124, leaving 17 time units of setup against a
// limit of 41.
//
// The row grants a licence rather than naming a value, so what the case claims
// is what the answer is not: the bval bit is clear, which is neither x nor z.
// Both 0 and 1 conform, and asserting either would pin a choice §31.6 leaves to
// the implementation. Issue #3413 is that the answer was x, which this rejects.
TEST(NotifierUpdateDriven, XNotifierBecomesKnownAfterADrivenViolation) {
  SimFixture f;
  const std::string kDesign = NotifierDesign("1'bx", 41, 107, 17);
  auto* notifier = RunAndFindVar(kDesign, f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 0u);
}

// Table 31-13's second row: BEFORE 0, AFTER 1. `d` rises at time 109 and `clk`
// rises at time 128, leaving 19 time units of setup against a limit of 43. The
// initial block writes the 0 before either transition, so the 1 read back is
// the update §31.6 requires and not a value the variable started at.
TEST(NotifierUpdateDriven, ZeroNotifierBecomesOneAfterADrivenViolation) {
  SimFixture f;
  const std::string kDesign = NotifierDesign("1'b0", 43, 109, 19);
  auto* notifier = RunAndFindVar(kDesign, f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  EXPECT_EQ(notifier->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 0u);
}

// Table 31-13's third row: BEFORE 1, AFTER 0. `d` rises at time 113 and `clk`
// rises at time 136, leaving 23 time units of setup against a limit of 47.
//
// Paired with the case above this is what shows the update reading the value it
// found: the two designs differ in the notifier's starting value alone, and a
// run that wrote one fixed value on every violation would fail one of the two
// whichever value it wrote.
TEST(NotifierUpdateDriven, OneNotifierBecomesZeroAfterADrivenViolation) {
  SimFixture f;
  const std::string kDesign = NotifierDesign("1'b1", 47, 113, 23);
  auto* notifier = RunAndFindVar(kDesign, f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  EXPECT_EQ(notifier->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 0u);
}

// §31.6 updates the notifier "whenever a timing violation occurs" and at no
// other time, so a satisfied window leaves it where the design put it. `d`
// rises at time 127 and `clk` rises at time 158, leaving 31 time units of setup
// against a limit of 29, so the window closes with nothing inside it and the
// notifier still holds the 0 the initial block wrote.
//
// Without this case a run that toggled the notifier on every reference edge
// would pass the 0-to-1 and 1-to-0 cases above, each of which drives exactly
// one reference edge and expects exactly one update.
//
// The absence of a report is stated with a null FindDiag, which selects by the
// message alone. That is the whole claim here, because every report the $setup
// site can make about any design carries this substring and there is no other
// report this case would tolerate.
TEST(NotifierUpdateDriven, SatisfiedWindowLeavesTheDrivenNotifierAtZero) {
  SimFixture f;
  auto* notifier =
      RunAndFindVar(NotifierDesign("1'b0", 29, 127, 31), f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_EQ(FindDiag(f, kSetupViolation), nullptr);
  EXPECT_EQ(notifier->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 0u);
}

}  // namespace
