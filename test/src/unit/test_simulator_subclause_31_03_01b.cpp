// Whether a running design's $setup and $hold checks are evaluated against the
// stimulus that design drives, and what a violation then produces: a report on
// the DiagEngine the run holds, and the notifier toggle of §31.6.
//
// Every case here writes a design, drives its two signals from an initial
// block, and reads back what the run recorded -- the diagnostics standing on
// the fixture, or the notifier variable the run left in SimContext. No case
// builds a TimingCheckEntry, and none calls
// SpecifyManager::CheckSetupViolation or SpecifyManager::CheckHoldViolation.
// That is what separates this file from test_simulator_subclause_31_03_01a.cpp
// beside it: every case there hands the predicate a reference time, a data time
// and a limit and asks for the verdict, so each proves the verdict is right
// once something asks and none proves that anything asks. Issue #3405 is that
// nothing did -- every caller of those predicates in the tree was a unit test,
// so no §31 violation was ever reported out of a run and no notifier ever
// toggled.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportViolation in src/simulator/timing_check_driver.cpp calls
// DiagEngine::Warning; the cases below read it through ReportedWarning rather
// than ReportedError. It stands at SourceLoc::None(), whose line is 0, because
// TimingCheckEntry records no position for the declaration it was built from.
//
// The two $setup cases share one design and differ in their stimulus alone.
// That is what shows a check being run rather than one answer being handed to
// both: a driver that reported unconditionally would fail the satisfied case,
// and a driver that reported nothing would fail the violating one.
//
// Only $setup (§31.3.1) and $hold (§31.3.2) are covered. The two windows run in
// opposite directions -- §31.3.1 ends its window at the reference edge and
// §31.3.2 begins its window there -- so the $hold case is not a restatement of
// the $setup ones. §31.3's other four stability checks, §31.4's clock and
// control checks and §31.9's negative checks are out of scope here.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, and so that no time is one another case's reference edge falls on. The
// limits are 23 (the two $setup cases, which are one design), 19 (the notifier
// case) and 17 ($hold), none of them the 0 a TimingCheckEntry::limit holds
// before a limit expression has been evaluated into it. The data transitions
// stand at 31, 11, 55 and 33 and the reference edges at 40, 74, 62 and 28,
// eight distinct times; the intervals they leave are 9, 63, 7 and 5, four more
// values distinct from each other, from every limit and from every time. So a
// case that read its interval, its limit or its edge out of another case's
// design would compare two numbers that disagree rather than two that happen to
// coincide.
//
// The notifier case does not reuse the violating $setup design's own literals,
// because doing so would put its reference edge at a time another case's edge
// falls on. What makes it the notifier case is that its check is violated and
// carries the optional notifier argument of Syntax 31-3, not that its numbers
// match another case's.
//
// Each source drives both signals to a known level before either transition
// that matters. TimingCheckEdgeMatches in src/simulator/timing_check_driver.cpp
// reads no edge out of a transition from x, so the x-to-0 assignments at time 0
// are not transitions any case counts, and each case's timeline begins at the
// first delay.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.
//
// Each check is written in the argument order its own syntax states: Syntax
// 31-3 writes `$setup(data_event, reference_event, limit [, notifier])` and
// Syntax 31-4 writes `$hold(reference_event, data_event, limit [, notifier])`,
// opposite orders. Parser::ParseTimingCheck in src/parser/parser_specify.cpp
// fills TimingCheckDecl::ref_terminal from the first argument for every check
// kind, and $setup is the one check of Clause 31 whose first argument is the
// data event, so the parser swaps the two for that kind alone. That swap and
// these cases landed together: without it a $setup arrived with its two signals
// in the fields named for the other, and the driver -- reading them by name --
// watched the clock edge as the timestamp and reported a $setup violation only
// where §31.3.2 would have wanted one.
//
// No case here reads either field and no message substring below names a
// signal, so nothing here would have recorded that inversion as intended even
// had it stood.
//
// §31.2 puts a system timing check inside a specify block, and
// CheckTimingTerminal in src/elaborator/elaborator_validate_specify.cpp
// enforces one rule over a check's terminals -- §25.6's ban on a `ref` port
// standing as one. §30.4.1's direction rules govern a module path's source and
// destination and not these, so a bare variable of the module serves as a
// terminal here.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborates, lowers and runs `design` on `f`. False when the source did not
// elaborate cleanly, which a case asserts on before reading anything off the
// fixture: a design rejected before it ran says nothing about §31 whatever the
// case was written to expect.
bool DrivenToCompletion(const std::string& design, SimFixture& f) {
  auto* rtl = ElaborateSrc(design, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

// §31.3.1: the window ends at the reference edge and opens `limit` time units
// before it, and a data transition strictly inside it is a violation. `d` rises
// at time 31 and `clk` rises at time 40, leaving 9 time units of setup against
// a limit of 23.
//
// The message substring stops before the signal name the report goes on to
// spell. What this case claims is that the violation was found and named as
// §31.3.1's, and naming a signal in the substring would tie it to which field
// each reached the report through as well.
TEST(DesignTimingCheckEvaluation, SetupViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      DrivenToCompletion("module top;\n"
                         "  logic d;\n"
                         "  logic clk;\n"
                         "  specify\n"
                         "    $setup(d, posedge clk, 23);\n"
                         "  endspecify\n"
                         "  initial begin\n"
                         "    d = 1'b0;\n"
                         "    clk = 1'b0;\n"
                         "    #31 d = 1'b1;\n"
                         "    #9 clk = 1'b1;\n"
                         "  end\n"
                         "endmodule\n",
                         f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$setup violation: data signal", 0, "31.3.1"));
}

// §31.3.1 again, and the same design: only the stimulus changes. `d` rises at
// time 11 and `clk` rises at time 74, leaving 63 time units of setup against
// the same limit of 23, so the window closes with nothing inside it.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $setup site can make about any design carries this substring and
// there is no other report this case would tolerate.
TEST(DesignTimingCheckEvaluation, SetupSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      DrivenToCompletion("module top;\n"
                         "  logic d;\n"
                         "  logic clk;\n"
                         "  specify\n"
                         "    $setup(d, posedge clk, 23);\n"
                         "  endspecify\n"
                         "  initial begin\n"
                         "    d = 1'b0;\n"
                         "    clk = 1'b0;\n"
                         "    #11 d = 1'b1;\n"
                         "    #63 clk = 1'b1;\n"
                         "  end\n"
                         "endmodule\n",
                         f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

// §31.6: the notifier the check was declared with is updated whenever that
// check detects a violation, which is the effect a design of its own can see
// and a diagnostic is not. `d` rises at time 55 and `clk` rises at time 62,
// leaving 7 time units against a limit of 19. The initial block writes 0 to the
// notifier before either transition, so the 1 read back after the run is
// Table 31-13's toggle and not a value the variable started at; a run that
// never evaluated the check leaves the 0 standing.
TEST(DesignTimingCheckEvaluation, SetupViolationInARunTogglesTheNotifier) {
  SimFixture f;
  auto* notifier = RunAndFindVar(
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  logic setup_notifier;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 19, setup_notifier);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    setup_notifier = 1'b0;\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #55 d = 1'b1;\n"
      "    #7 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_EQ(notifier->value.ToUint64(), 1u);
}

// §31.3.2: the window begins at the reference edge and closes `limit` time
// units after it, running forwards where §31.3.1's runs backwards, so a driver
// written for one order does not answer the other. `clk` rises at time 28 and
// `d` rises at time 33, leaving 5 time units of hold against a limit of 17.
TEST(DesignTimingCheckEvaluation, HoldViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      DrivenToCompletion("module top;\n"
                         "  logic d;\n"
                         "  logic clk;\n"
                         "  specify\n"
                         "    $hold(posedge clk, d, 17);\n"
                         "  endspecify\n"
                         "  initial begin\n"
                         "    d = 1'b0;\n"
                         "    clk = 1'b0;\n"
                         "    #28 clk = 1'b1;\n"
                         "    #5 d = 1'b1;\n"
                         "  end\n"
                         "endmodule\n",
                         f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$hold violation: data signal", 0, "31.3.2"));
}

}  // namespace
