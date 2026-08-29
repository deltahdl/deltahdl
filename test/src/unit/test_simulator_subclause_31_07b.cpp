// Whether §31.7's `&&&` conditioned event reaches a running design: whether a
// conditioned timing check is evaluated when its condition holds and passed
// over when it does not, read back from what the run reported.
//
// Every case here writes a design, drives its signals from an initial block,
// and reads the diagnostics standing on the fixture afterwards. No case builds
// an Expr, a TimingCheckEntry or a TimingCheckConditionKind, and none calls
// ClassifyTimingCheckCondition, TimingCheckConditionEnables or
// IsDeterministicTimingCheckCondition. That is what separates this file from
// test_simulator_subclause_31_07a.cpp beside it: every case there hands the
// classifier a parsed condition or hands the enable predicate a kind and a
// value and asks for the verdict, so each proves §31.7 is answered once
// something asks, and none proves that a run asks. Issue #3410 is that nothing
// did -- TimingCheckEntry carried the condition's rendered text for §32.4.1's
// SDF COND matching and no expression the run could evaluate, so every §31
// watcher fired on the transition alone and a conditioned check reported a
// violation whether or not its condition held.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportViolation in src/simulator/timing_check_driver.cpp calls
// DiagEngine::Warning; the cases below read it through ReportedWarning rather
// than ReportedError. The report stands on the line the check was written on.
// TimingCheckEntry::loc in src/simulator/specify_timing_check.h carries that
// line, Parser::ParseTimingCheck in src/parser/parser_specify.cpp having
// recorded the check's own first token into the declaration it was built from.
// Each case names that line through LineHolding rather than writing a number,
// so a case cannot drift when its design gains or loses a line. Issue #3414 is
// that the report stood at SourceLoc::None(), whose line is 0, before
// TimingCheckEntry carried a source position.
//
// The first two cases share one design and one stimulus and differ in the value
// of the conditioning signal alone. That is what shows the condition being read
// rather than one answer being handed to both: a driver that ignored the
// condition would report in both, and a driver that read it as always false
// would report in neither.
//
// The x cases are the pair §31.7 divides by the operator written in the
// condition. "When comparisons are deterministic, an x value on the
// conditioning signal shall not enable the timing check", and the clause lists
// the bare `expression` form -- no operation -- among the deterministic ones,
// so the plain `&&& en` case reports nothing with `en` at x. "For
// nondeterministic comparisons, an x on the conditioning signal shall enable
// the timing check", and `==` is one of the two nondeterministic forms, so the
// `&&& (en == 1'b1)` case reports with the same x standing on the same signal.
//
// The `~en` case is where a fix that evaluated the whole condition expression
// would go wrong. §31.7 states its rule over the value of the conditioning
// signal, and TimingCheckConditionEnables in
// src/simulator/specify_timing_violation.cpp applies the `~` itself, so
// TimingCheckConditioningSignal hands it the operand rather than the negation.
// Evaluating `~en` and passing that would invert twice: `en` at 0 would arrive
// as 1, the negate form would read it as disabled, and the case would report
// nothing where §31.7 wants a report.
//
// The $hold case carries its condition on the data event rather than the
// reference event, so a driver that read TimingCheckEntry::ref_condition_expr
// alone would evaluate the check and report. §31.7 attaches a condition to the
// timing_check_event it follows, and the two events of a check are gated
// separately.
//
// Each check is written in the argument order its own syntax states: Syntax
// 31-3 writes `$setup(data_event, reference_event, limit)`, the one check of
// Clause 31 whose first argument is the data event, and Syntax 31-4 writes
// `$hold(reference_event, data_event, limit)`. Parser::ParseTimingCheck in
// src/parser/parser_specify.cpp swaps the two for $setup alone, conditions
// included, so the `&&&` written on `posedge clk` in a $setup reaches
// TimingCheckEntry::ref_condition_expr.
//
// The literals are picked so that no two quantities a case tells apart share a
// value. The limits are 29 (the two conditioning-value cases, which are one
// design and one stimulus), 37 (the plain condition at x), 41 (the equality
// condition at x), 53 (the negated condition) and 67 ($hold), none of them the
// 0 a TimingCheckEntry::limit holds before a limit expression has been
// evaluated into it. The transitions stand at 13, 19, 22, 30, 44, 55, 61, 76,
// 83 and 92, ten distinct times, and the intervals they leave are 6, 8, 11, 15
// and 9, five more values distinct from each other, from every limit and from
// every time. So a case that read its interval, its limit or its edge out of
// another case's design would compare two numbers that disagree rather than two
// that happen to coincide.
//
// Every stimulus violates its check's window, because a satisfied window
// reports nothing whatever the condition says and could not tell a suppressed
// check from a passing one. What each case varies is the condition alone.
//
// Each source drives every signal to a known level before any transition that
// matters. TimingCheckEdgeMatches in
// src/simulator/timing_check_driver_internal.h reads no edge out of a
// transition from x, so the x-to-0 assignments at time 0 are not transitions
// any case counts, and each case's timeline begins at the first delay. The two
// cases whose conditioning signal stands at x assign it 1'bx outright, so the
// value §31.7's x rule is applied to is one the source states rather than one
// left over from a variable nothing wrote.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// Elaborates, lowers and runs `design` on `f`. False when the source did not
// elaborate cleanly, which a case asserts on before reading anything off the
// fixture: a design rejected before it ran says nothing about §31.7 whatever
// the case was written to expect.
bool DrivenToCompletion(const std::string& design, SimFixture& f) {
  auto* rtl = ElaborateSrc(design, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

// §31.7: the conditioning signal is 0, so the reference event never occurs and
// the check is not evaluated, though the stimulus violates §31.3.1's window --
// `d` rises at time 13 and `clk` rises at time 19, leaving 6 time units of
// setup against a limit of 29. This is the defect issue #3410 names: before the
// condition reached the run, this design reported.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $setup site can make about any design carries this substring and
// there is no other report this case would tolerate.
TEST(ConditionedTimingCheckEvaluation, SetupWithFalseConditionReportsNothing) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& en, 29);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'b0;\n"
      "    #13 d = 1'b1;\n"
      "    #6 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

// §31.7 with the same design and the same stimulus as the case above, the
// conditioning signal alone changed: `en` stands at 1, so the reference event
// occurs and §31.3.1's window is evaluated over the 6 time units of setup a
// limit of 29 requires more of.
//
// The message substring stops before the signal name the report goes on to
// spell. What this case claims is that the violation was found and named as
// §31.3.1's, and naming a signal in the substring would tie it to which field
// each reached the report through as well.
TEST(ConditionedTimingCheckEvaluation, SetupWithTrueConditionIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& en, 29);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'b1;\n"
      "    #13 d = 1'b1;\n"
      "    #6 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, posedge clk &&& en"), "31.3.1"));
}

// §31.7: "When comparisons are deterministic, an x value on the conditioning
// signal shall not enable the timing check", and the bare `expression` form --
// the clause's "no operation" -- is deterministic, so `en` at x leaves the
// check disabled. `d` rises at time 22 and `clk` rises at time 30, leaving 8
// time units of setup against a limit of 37, which §31.3.1 would report were
// the check enabled at all.
TEST(ConditionedTimingCheckEvaluation, PlainConditionAtXReportsNothing) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& en, 37);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'bx;\n"
      "    #22 d = 1'b1;\n"
      "    #8 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

// §31.7: "For nondeterministic comparisons, an x on the conditioning signal
// shall enable the timing check", and `==` is one of the two nondeterministic
// forms, so the same x that disables the plain form above enables this one. `d`
// rises at time 44 and `clk` rises at time 55, leaving 11 time units of setup
// against a limit of 41.
TEST(ConditionedTimingCheckEvaluation, EqualityConditionAtXIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& (en == 1'b1), 41);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'bx;\n"
      "    #44 d = 1'b1;\n"
      "    #11 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, posedge clk &&& (en == 1'b1)"),
      "31.3.1"));
}

// §31.7 reads the value of the conditioning signal and applies the `~` itself,
// so `en` at 0 enables the check and §31.3.1 reports over the 15 time units of
// setup `d` at time 61 leaves `clk` at time 76, against a limit of 53. A fix
// that evaluated the whole condition expression and then applied `~` again
// would invert twice -- `~en` evaluates to 1 with `en` at 0, the negate form
// reads a 1 as disabled -- and would report nothing here.
TEST(ConditionedTimingCheckEvaluation, NegatedConditionAtZeroIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& ~en, 53);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'b0;\n"
      "    #61 d = 1'b1;\n"
      "    #15 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, posedge clk &&& ~en"), "31.3.1"));
}

// §31.7 attaches a condition to the timing_check_event it follows, and here
// that is the data event of a $hold: Syntax 31-4 writes
// `$hold(reference_event, data_event, limit)`, so the `&&& en` rides on `d`.
// With `en` at 0 the data event never occurs and §31.3.2's window is never
// closed, though `clk` rises at time 83 and `d` at time 92, leaving 9 time
// units of hold against a limit of 67. A driver reading
// TimingCheckEntry::ref_condition_expr alone would find the null condition of
// the unconditioned reference event, gate nothing, and report.
TEST(ConditionedTimingCheckEvaluation,
     HoldWithFalseDataConditionReportsNothing) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  logic en;\n"
      "  specify\n"
      "    $hold(posedge clk, d &&& en, 67);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'b0;\n"
      "    #83 clk = 1'b1;\n"
      "    #9 d = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$hold violation: data signal"), nullptr);
}

}  // namespace
