// Whether §31.8's vector rule reaches a running design: whether a timing check
// whose signal is a vector is evaluated on a transition of any one of that
// signal's bits, and whether several bits transitioning at one moment still
// produce one report, read back from what the run reported.
//
// Every case here writes a design, drives its signals from an initial block,
// and reads the diagnostics standing on the fixture afterwards. No case builds
// a TimingCheckEntry or a SpecifyManager, and none calls
// IsSingleSignalTimingCheck, TimingCheckExpandedCount,
// VectorTransitionViolationCount or ToggleNotifierOnViolation. That is what
// separates this file from test_simulator_subclause_31_08a.cpp beside it: every
// case there hands one of those four functions a kind, a pair of widths or a
// pair of values and asks for the answer, so each proves §31.8 is answered once
// something asks, and none drives a design at all. Issue #3412 is that a run
// did not ask across the whole vector -- WatchEdge in
// src/simulator/timing_check_driver_internal.h reduced a value to the level of
// its least significant bit, so a transition on any other bit was neither seen
// nor checked. WatchEdge now keeps the level of every bit through LevelsOfBits,
// and TimingCheckSignalTransitioned answers true when any one bit makes the
// transition the edge names.
//
// §31.8 states the default and states the option separately, and the default is
// what a run implements. "Either or both signals in a timing check can be a
// vector. This shall be interpreted as a single timing check where the
// transition of one or more bits of a vector is considered a single transition
// of that vector." The clause then allows that "simulators may provide an
// option causing vectors in timing checks to result in the creation of multiple
// single-bit timing checks", under which a $width over a vector of width N
// becomes N checks and a $setup over signals of widths M and N becomes M*N.
// deltahdl provides no such option, so every case below expects the single
// check and the single report of the default, and no case below expects a
// per-bit count.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportTimingViolation in src/simulator/timing_check_driver_internal.h calls
// DiagEngine::Warning; the cases below read it through ReportedWarning rather
// than ReportedError. It stands on the line the check was written on.
// TimingCheckEntry::loc in src/simulator/specify_timing_check.h carries that
// line, and Parser::ParseTimingCheck in src/parser/parser_specify.cpp sets it
// to the location of the check's own first token. Each case below names the
// line through LineHolding in lib/cpp/test_helpers/helpers_reported_error.h
// rather than writing a number, so no case drifts when its design gains or
// loses a line. Issue #3414 is the defect that left the line 0: nothing
// carried the position from the declaration to the run, so the report stood at
// SourceLoc::None().
//
// Two cases count reports rather than name one, which is what §31.8 states
// outright for them. Of a $setup whose 8-bit data signal changes in six bits at
// one moment the clause says the check "shall still only report a single timing
// violation", so the number of reports is the rule here rather than a stand-in
// for it, and a case that only found one report would pass with a run that made
// six. Each of the two states the claim in two steps: ReportedWarning names the
// message, the line and the subclause of the report that was made, and
// FindDiagFrom (lib/cpp/test_fixtures/fixture_simulator.h) started one past
// that report's position says there is no second one. The first step is what
// keeps the second honest, a run that reported nothing at all having no second
// report either.
//
// The first three cases share one design and differ in the value driven onto
// the two-bit reference signal alone. That is what shows every bit being
// watched rather than one chosen bit being watched: a driver reading the least
// significant bit reports in the second and not in the first, one reading the
// most significant bit reports in the first and not in the second, and one
// reading every bit reports in both.
//
// The fourth and fifth cases put the vector on the data signal of a $setup and
// leave its reference signal a scalar. The two sides of a check are read by
// separate watchers armed on separate variables in ArmStabilityWindow
// (src/simulator/timing_check_driver.cpp), so a data side still read at one bit
// fails these two and passes the first three.
//
// The sixth case is §31.4.4's $width, whose two edges are two transitions of
// one signal: the clause leaves the data event implicit and has it triggered by
// the transition opposite the reference event's, so the pulse this case
// measures opens when the vector's upper bit rises and closes when that same
// bit falls. A driver
// reading the lower bit finds neither edge and measures no pulse.
//
// The vectors are declared over ranges that do not begin at zero -- `logic
// [5:4]`, `logic [7:4]` and `logic [3:2]` -- so that no bit's index within the
// declaration equals its offset within the stored value. §11.5.1 makes the
// declaration decide which bit an index reaches, and a `[N:0]` declaration
// makes the two numbers the same for every bit, under which code that walked
// indices where offsets were required would answer correctly anyway. Each case
// then assigns the whole vector in one statement rather than through a
// part-select, so what the case turns on is which bit of the value moved and
// never which index the source wrote.
//
// The literals are picked so that no two quantities a case tells apart share a
// value. The limits are 73 (the three reference-vector cases, which are one
// design), 79 (the two data-vector cases, which are a second design) and 89
// (the $width case), none of them the 0 a TimingCheckEntry::limit holds before
// a limit expression has been evaluated into it. The transitions stand at times
// 223, 229, 233, 234, 239, 241, 242, 250, 251, 262, 270 and 282, and the
// intervals they leave are 11, 13, 17, 23, 29 and 31, six values distinct from
// each other, from every limit and from every time. So a case that read its
// interval, its limit or its edge out of another case's design would compare
// two numbers that disagree rather than two that happen to coincide.
//
// The $width case writes its threshold as 0, which is the value §31.4.4 gives
// it when it is left out, and no case here turns on it. Issue #3418 is why: a
// declared threshold never reaches the registered check, because
// BuildTimingCheckUnderOptions in src/simulator/specify_timing_check.cpp never
// assigns TimingCheckEntry::threshold, so a case whose expected answer depended
// on a non-zero threshold would fail on that defect rather than on §31.8.
//
// Every stimulus violates its check's window, because a satisfied window
// reports nothing whatever the bits did and could not tell a check that never
// fired from one that passed. What each case varies is which bits moved.
//
// Each source drives every signal to a known level before any transition that
// matters. §31.5 makes posedge the shorthand for edge[01, 0x, x1], so the
// x-to-0 assignments at time 0 are no posedge and open no window, and each
// case's timeline begins at the first delay. The data event of a $setup carries
// no edge_control_specifier and so matches every transition, the x-to-0
// assignment included, which is why the two data-vector cases carry limits
// short enough that the timestamp left at time 0 falls outside the window their
// reference edge closes.
//
// Each source is one module named `top`, and it is the only module, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.
//
// Syntax 31-3 writes `$setup(data_event, reference_event,
// timing_check_limit)`, the one check of Clause 31 whose first argument is the
// data event. Syntax 31-12 writes `$width(controlled_reference_event,
// timing_check_limit, threshold [, [notifier]])`.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The part of a §31.3.1 report that names the rule without naming a signal.
// ReportViolation in src/simulator/timing_check_driver.cpp goes on to spell the
// two signals the check measures between, and a case naming one of them in the
// substring would tie its claim to which field each reached the report through
// as well.
//
// It is a constant rather than a literal at each site because the two counting
// cases below write it twice, once to name the report that was made and once to
// ask for a second: the two halves state one claim, and a substring that
// differed between them would leave the second half asking about some other
// report.
constexpr std::string_view kSetupViolation = "$setup violation: data signal";

// The same for §31.4.4, whose report ReportPulseViolation in
// src/simulator/timing_check_pulse.cpp goes on to spell a signal, an elapsed
// time and a limit into.
constexpr std::string_view kWidthViolation = "$width violation: signal";

// Elaborates, lowers and runs `design` on `f`. False when the source did not
// elaborate cleanly, which a case asserts on before reading anything off the
// fixture: a design rejected before it ran says nothing about §31.8 whatever
// the case was written to expect.
bool DrivenToCompletion(const std::string& design, SimFixture& f) {
  auto* rtl = ElaborateSrc(design, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

// The position in `f`'s diagnostics of the first whose message contains
// `needle`, or the number of diagnostics when none does. A case that claims one
// report and no second passes this position plus one to FindDiagFrom, so what
// it asks for is a report beyond the one it already named rather than a report
// beyond a position it guessed.
std::size_t PositionOfFirstDiag(const SimFixture& f, std::string_view needle) {
  const auto& diags = f.diag.Diagnostics();
  for (std::size_t i = 0; i < diags.size(); ++i) {
    if (diags[i].message.find(needle) != std::string::npos) return i;
  }
  return diags.size();
}

// The design the first three cases share: a $setup whose reference signal is
// the two-bit vector §31.8 allows, with `stimulus` as the tail of its initial
// block. `clk` is declared [5:4], so its upper bit stands at offset 1 of the
// stored value and its lower bit at offset 0, and neither offset equals the
// index the declaration gives that bit.
std::string VectorReferenceDesign(const std::string& stimulus) {
  return std::string(
             "module top;\n"
             "  logic d;\n"
             "  logic [5:4] clk;\n"
             "  specify\n"
             "    $setup(d, posedge clk, 73);\n"
             "  endspecify\n"
             "  initial begin\n"
             "    d = 1'b0;\n"
             "    clk = 2'b00;\n") +
         stimulus +
         "  end\n"
         "endmodule\n";
}

// The design the fourth and fifth cases share: a $setup whose data signal is a
// four-bit vector and whose reference signal is a scalar. `d` is declared
// [7:4], so its bits stand at offsets 0 through 3 of the stored value under
// indices 4 through 7.
std::string VectorDataDesign(const std::string& stimulus) {
  return std::string(
             "module top;\n"
             "  logic [7:4] d;\n"
             "  logic clk;\n"
             "  specify\n"
             "    $setup(d, posedge clk, 79);\n"
             "  endspecify\n"
             "  initial begin\n"
             "    d = 4'b0000;\n"
             "    clk = 1'b0;\n") +
         stimulus +
         "  end\n"
         "endmodule\n";
}

// §31.8: "the transition of one or more bits of a vector is considered a single
// transition of that vector", so the upper bit of `clk` rising is `clk` rising
// and the posedge reference event of the $setup occurs. `d` rises at time 223
// and `clk` takes the value 2'b10 at time 234, leaving 11 time units of setup
// against a limit of 73, which §31.3.1 reports. The lower bit of `clk` holds
// the 0 it was driven to at time 0 throughout, so a driver reading that bit
// alone finds no reference event at all and reports nothing. That is the defect
// issue #3412 names.
TEST(VectorSignalsInTimingChecksDriven,
     VectorReferenceUpperBitRisingAloneIsReported) {
  SimFixture f;
  const std::string kDesign = VectorReferenceDesign(
      "    #223 d = 1'b1;\n"
      "    #11 clk = 2'b10;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
}

// §31.8 with the same design as the case above, the bit that rises alone
// changed: `clk` takes the value 2'b01, so its lower bit rises and its upper
// bit holds the 0 it was driven to at time 0. `d` rises at time 229 and `clk`
// rises at time 242, leaving 13 time units of setup against the same limit of
// 73. Paired with the case above this is what shows every bit of the vector
// being watched: a driver watching one chosen bit reports in exactly one of the
// two.
TEST(VectorSignalsInTimingChecksDriven,
     VectorReferenceLowerBitRisingAloneIsReported) {
  SimFixture f;
  const std::string kDesign = VectorReferenceDesign(
      "    #229 d = 1'b1;\n"
      "    #13 clk = 2'b01;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
}

// §31.8: "This shall be interpreted as a single timing check where the
// transition of one or more bits of a vector is considered a single transition
// of that vector", and of its own example the clause says the check "shall
// still only report a single timing violation". Both bits of `clk` rise in the
// one assignment at time 250, and the $setup reports once. `d` rises at time
// 233, leaving 17 time units of setup against the same limit of 73 the two
// cases above use.
//
// The number of reports is the claim here, which CLAUDE.md otherwise warns
// against: a count states how many reports a run made and nothing about which
// rule any of them enforced. §31.8 states the number outright, so here the
// number is the rule rather than a stand-in for it, and a run that treated each
// transitioned bit as its own check would report twice and satisfy every
// assertion that only asked whether §31.3.1 had fired. The two steps are
// ReportedWarning, which says the report was made and names the rule it
// enforces, and FindDiagFrom started one past that report, which says there is
// no second.
TEST(VectorSignalsInTimingChecksDriven,
     VectorReferenceBothBitsRisingAtOnceReportsOnce) {
  SimFixture f;
  const std::string kDesign = VectorReferenceDesign(
      "    #233 d = 1'b1;\n"
      "    #17 clk = 2'b11;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  std::size_t first = PositionOfFirstDiag(f, kSetupViolation);
  EXPECT_EQ(FindDiagFrom(f, first + 1, kSetupViolation), nullptr);
}

// §31.8 applied to the data signal of a $setup, the reference signal being a
// scalar: `d` takes the value 4'b1000 at time 239, so the bit at offset 3
// transitions and the other three hold the 0 they were driven to at time 0.
// That is a transition of `d`, and `clk` rises at time 262, leaving 23 time
// units of setup against a limit of 79.
//
// The two sides of a check are watched separately, so this fails separately
// from the reference-vector cases above: a driver that read the reference
// signal across every bit and the data signal at offset 0 alone would find the
// posedge at time 262 and measure it against the x-to-0 transition at time 0,
// which is 262 time units back and outside a window 79 wide, and would report
// nothing.
TEST(VectorSignalsInTimingChecksDriven,
     VectorDataUpperBitTransitioningAloneIsReported) {
  SimFixture f;
  const std::string kDesign = VectorDataDesign(
      "    #239 d = 4'b1000;\n"
      "    #23 clk = 1'b1;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
}

// §31.8's own example in miniature. The clause's is a `module DFF` with `input
// CLK; input [7:0] DAT;` and `$setup (DAT, posedge CLK, 10);`, of which it says
// that if DAT "transitions from 'b00101110 to 'b01010011 at time 100 and if CLK
// transitions from 0 to 1 at time 105, then the $setup timing check shall still
// only report a single timing violation". Here `d` takes the value 4'b1110 at
// time 241, so three of its four bits transition in one assignment, and `clk`
// rises at time 270, leaving 29 time units of setup against the same limit of
// 79 the case above uses. The $setup reports once.
//
// The number of reports is the claim, for the reason the both-bits case above
// gives: §31.8 states the number, so a run creating one check per transitioned
// bit would report three times and is what this tells apart from the single
// check §31.8 requires. The bit at offset 0 holds its 0, so this also fails
// under a driver reading the data signal at that bit alone.
TEST(VectorSignalsInTimingChecksDriven,
     VectorDataSeveralBitsTransitioningAtOnceReportsOnce) {
  SimFixture f;
  const std::string kDesign = VectorDataDesign(
      "    #241 d = 4'b1110;\n"
      "    #29 clk = 1'b1;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  std::size_t first = PositionOfFirstDiag(f, kSetupViolation);
  EXPECT_EQ(FindDiagFrom(f, first + 1, kSetupViolation), nullptr);
}

// §31.8 applied to §31.4.4's $width, whose one signal is the two-bit vector
// `clk` declared [3:2]. §31.4.4 leaves the data event implicit, it and the
// reference event being "triggered by opposite transitions", so the pulse opens
// on the posedge and closes on the negedge of the same signal, and both are
// found across every bit. `clk` takes the value 2'b10 at time 251 and returns
// to 2'b00 at time 282, holding its level for 31 time units against a limit
// of 89. The lower bit holds the 0 it was driven to at time 0 through both, so
// a driver reading that bit alone finds neither edge, measures no pulse and
// reports nothing.
TEST(VectorSignalsInTimingChecksDriven,
     VectorWidthPulseOnUpperBitAloneIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic [3:2] clk;\n"
      "  specify\n"
      "    $width(posedge clk, 89, 0);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    clk = 2'b00;\n"
      "    #251 clk = 2'b10;\n"
      "    #31 clk = 2'b00;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kWidthViolation,
                              LineHolding(kDesign, "$width(posedge clk,"),
                              "31.4.4"));
}

}  // namespace
