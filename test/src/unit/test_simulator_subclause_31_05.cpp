// Whether §31.5's edge_control_specifier written in its general form decides
// which transitions a Clause 31 timing check answers to, read back from what a
// run reported.
//
// Every case here writes a design, drives its signals from an initial block,
// and reads the diagnostics standing on the fixture afterwards. No case builds
// a TimingCheckDecl or a TimingCheckEntry, none calls TimingCheckEdgeMatches or
// WatchEdge, and none reads TimingCheckEntry::ref_edge_descriptors back. That
// is what separates this file from test_parser_subclause_31_05.cpp: every case
// there parses a specify block and reads the list off
// TimingCheckDecl::ref_edge_descriptors, so each proves the descriptors were
// recorded and none proves that a run consults them. Issue #3411 is that no run
// did. BuildTimingCheckUnderOptions in src/simulator/specify_timing_check.cpp
// put only the SpecifyEdge::kEdge saying the general form had been written into
// TimingCheckEntry, the parsed list stopped at the declaration, and every
// watcher armed for an `edge[...]` event therefore matched every transition:
// `edge[01] clk` reported on a fall and on a transition to x as readily as on a
// rise.
//
// A timing violation is reported as a warning and not as an error. The design
// is legal and the run reaches a state the design said it should not, so
// ReportTimingViolation in src/simulator/timing_check_driver_internal.h calls
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
// §31.5 gives six edge_descriptors and no more: Syntax 31-15 writes
// `edge_descriptor ::= 01 | 10 | z_or_x zero_or_one | zero_or_one z_or_x`, and
// the clause spells the six out as 01, 0x, 10, 1x, x0 and x1. It also states
// that "edge transitions involving z are treated the same way as edge
// transitions involving x", which is why the `edge[z1]` case expects the same
// answer an `edge[x1]` case would get.
//
// §31.5 makes the two shorthands lists of those descriptors rather than a
// second kind of edge: `posedge clr` "is equivalent to" `edge[01, 0x, x1] clr`,
// and `negedge clr` "is the same as" `edge[10, x0, 1x] clr`. The three
// `edge[01, 0x, x1]` cases are that equivalence read one descriptor at a time,
// so the general form and the shorthand agree on all three transitions a
// posedge admits. The `edge[01]` and `edge[1x]` cases are the other half of
// §31.5, that "edge-control specifiers offer the flexibility to declare edge
// transitions other than posedge and negedge": each names one descriptor of a
// shorthand's list and is answered by that descriptor alone.
//
// The first two cases share one design, one limit and one stimulus, and differ
// in the value the clock arrives at. That is what shows the descriptor list
// being read rather than one answer being handed to both: a driver that matched
// every transition would report in both, and a driver that matched none would
// report in neither. The three `edge[01, 0x, x1]` cases likewise share one
// design and one limit.
//
// The `edge[1x]` case is where a matcher that fell back to §31.5's shorthands
// would go wrong. `1x` is in the list `negedge` abbreviates, so a driver that
// read a list containing `1x` as a negedge would answer to the `10` in the same
// list; Syntax 31-15 makes `10` and `1x` separate edge_descriptors, and naming
// one names nothing about the other.
//
// The two $width cases turn on §31.4.4's derived data event: "data event =
// reference event signal with opposite edge", Table 31-10 making the data event
// implicit and Syntax 31-12 writing `$width(controlled_reference_event,
// timing_check_limit, threshold [, [notifier]])` with no place to declare one.
// §31.4.4 does not define the opposite of an arbitrary edge_control_specifier;
// it names an opposite for posedge and negedge and says nothing about reversing
// an edge_descriptor list. OppositeEdge in src/simulator/timing_check_pulse.cpp
// reverses each descriptor of the list, and §31.5 is what makes that the right
// reading: reversing every descriptor of `edge[01, 0x, x1]` gives
// `edge[10, x0, 1x]`, which is exactly the pair of lists §31.5 gives for
// posedge and negedge. So `edge[01]` opens the pulse and `edge[10]` closes it,
// and the clock leaving the pulse by going 1 to x closes nothing, `1x` not
// being the reverse of `01`.
//
// The threshold is written as 0, the value §31.4.4 gives it when it is left
// out, and no case here turns on it. Issue #3418 is why: a declared threshold
// never reaches the registered check.
//
// Every stimulus violates its check's window, because a satisfied window
// reports nothing whatever the edge says and could not tell a suppressed check
// from a passing one. What each case varies is the transition alone.
//
// The literals are picked so that no two quantities a case tells apart share a
// value. The limits are 23 (the two `edge[01]` $setup cases, which are one
// design and one stimulus), 31 (the three `edge[01, 0x, x1]` cases), 43
// (`edge[1x]`), 59 (`edge[z1]`) and 71 (the two $width cases), none of them the
// 0 a TimingCheckEntry::limit holds before a limit expression has been
// evaluated into it. The transitions stand at 101, 106, 113, 120, 127, 136,
// 149, 160, 167, 180, 181, 191, 194, 198, 211 and 215, sixteen distinct times,
// and the intervals they leave are 3, 4, 5, 7, 9, 11, 13 and 17, eight more
// values distinct from each other, from every limit and from every time. So a
// case that read its interval, its limit or its edge out of another case's
// design would compare two numbers that disagree rather than two that happen to
// coincide.
//
// Each source drives every signal to a known level before any transition the
// case counts. TimingCheckEdgeMatches reads no transition out of a value that
// did not change, so a signal a case wants to leave x is assigned 1'bx outright
// at time 0 and the run's first transition on it is the one the case names. The
// x-to-0 and x-to-1 assignments at time 0 are `x0` and `x1` transitions, and no
// case declares a descriptor either of them matches.
//
// Syntax 31-3 writes `$setup(data_event, reference_event, timing_check_limit)`,
// the one check of Clause 31 whose first argument is the data event, so the
// `edge[...]` of a $setup case goes on the second argument and reaches
// TimingCheckEntry::ref_edge_descriptors. The data event carries no edge, which
// Syntax 31-2 allows and which §31.5 leaves unrestricted, so `d` rising is what
// opens §31.3.1's window in every $setup case.
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
// fixture: a design rejected before it ran says nothing about §31.5 whatever
// the case was written to expect.
bool DrivenToCompletion(const std::string& design, SimFixture& f) {
  auto* rtl = ElaborateSrc(design, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

// §31.5: `edge[01]` names one edge_descriptor, and `clk` going from 0 to x is
// the `0x` Syntax 31-15 lists separately, so the reference event never occurs
// and §31.3.1's window is never closed. The stimulus violates that window --
// `d` rises at time 101 and `clk` leaves 0 at time 106, leaving 5 time units of
// setup against a limit of 23 -- so a driver that matched every transition
// would report here. That is the defect issue #3411 names.
//
// Absence is the claim, and ReportedWarning cannot state it: it answers that
// some diagnostic matched a message, a line and a subclause, and there is no
// negation of all three. The acceptance form is a null FindDiag, which selects
// by the message alone -- and here that is the whole claim, because every
// report the $setup site can make about any design carries this substring and
// there is no other report this case would tolerate.
TEST(EdgeControlSpecifierEvaluation, SetupEdge01IgnoresAZeroToXTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $setup(d, edge[01] clk, 23);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #101 d = 1'b1;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

// §31.5 with the same design, the same limit and the same stimulus as the case
// above, the value `clk` arrives at alone changed: 0 to 1 is the `01` the
// specifier names, so the reference event occurs and §31.3.1's window is
// evaluated over the 5 time units of setup a limit of 23 requires more of.
//
// The message substring stops before the signal name the report goes on to
// spell. What this case claims is that the violation was found and named as
// §31.3.1's, and naming a signal in the substring would tie it to which field
// each reached the report through as well.
TEST(EdgeControlSpecifierEvaluation, SetupEdge01AnswersToAZeroToOneTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $setup(d, edge[01] clk, 23);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #101 d = 1'b1;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[01] clk"), "31.3.1"));
}

// §31.5: `edge[01, 0x, x1] clr` is what the clause makes `posedge clr`
// equivalent to, and this is the first of its three descriptors. `d` rises at
// time 113 and `clk` rises at time 120, leaving 7 time units of setup against a
// limit of 31.
TEST(EdgeControlSpecifierEvaluation, PosedgeListAnswersToAZeroToOneTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $setup(d, edge[01, 0x, x1] clk, 31);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #113 d = 1'b1;\n"
      "    #7 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[01, 0x, x1] clk"), "31.3.1"));
}

// §31.5 with the same design and the same limit as the case above: the second
// of the three descriptors `posedge` abbreviates. `clk` goes from 0 to x, which
// the `edge[01]` case rejects and this list accepts, so the same transition
// gets opposite answers from two specifiers that differ in their descriptors
// alone. `d` rises at time 127 and `clk` leaves 0 at time 136, leaving 9 time
// units of setup against a limit of 31.
TEST(EdgeControlSpecifierEvaluation, PosedgeListAnswersToAZeroToXTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $setup(d, edge[01, 0x, x1] clk, 31);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #127 d = 1'b1;\n"
      "    #9 clk = 1'bx;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[01, 0x, x1] clk"), "31.3.1"));
}

// §31.5 with the same design and the same limit again: the third of the three
// descriptors `posedge` abbreviates. `clk` is assigned 1'bx at time 0 so that
// the transition this case counts leaves x rather than the level a variable
// nothing wrote happens to hold, and that assignment changes no value and is no
// transition. `d` rises at time 149 and `clk` reaches 1 at time 160, leaving 11
// time units of setup against a limit of 31.
TEST(EdgeControlSpecifierEvaluation, PosedgeListAnswersToAnXToOneTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $setup(d, edge[01, 0x, x1] clk, 31);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'bx;\n"
      "    #149 d = 1'b1;\n"
      "    #11 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[01, 0x, x1] clk"), "31.3.1"));
}

// §31.5: `edge[1x]` names the `1x` of `negedge`'s list and not the `10` beside
// it, so `clk` falling from 1 to 0 is not the reference event and §31.3.1's
// window is never closed. `clk` is assigned 1 at time 0, which is the `x1` no
// descriptor here names. `d` rises at time 167 and `clk` falls at time 180,
// leaving 13 time units of setup against a limit of 43, which §31.3.1 would
// report were the transition matched at all. A matcher that read a list drawn
// from `negedge`'s three descriptors as a negedge would report here.
TEST(EdgeControlSpecifierEvaluation, SetupEdge1xIgnoresAOneToZeroTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $setup(d, edge[1x] clk, 43);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b1;\n"
      "    #167 d = 1'b1;\n"
      "    #13 clk = 1'b0;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

// §31.5: "Edge transitions involving z are treated the same way as edge
// transitions involving x", so `edge[z1]` is answered by a transition from x to
// 1. `clk` is assigned 1'bx at time 0, which changes no value and is no
// transition, and reaches 1 at time 198. `d` rises at time 181, leaving 17 time
// units of setup against a limit of 59.
TEST(EdgeControlSpecifierEvaluation, SetupEdgeZ1AnswersToAnXToOneTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic d;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $setup(d, edge[z1] clk, 59);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'bx;\n"
      "    #181 d = 1'b1;\n"
      "    #17 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[z1] clk"), "31.3.1"));
}

// §31.4.4 with a reference event written in §31.5's general form: `edge[01]`
// opens the pulse and its reverse `edge[10]` closes it, the clause deriving the
// data event as "reference event signal with opposite edge". `clk` rises at
// time 191 and falls at time 194, holding its level for 3 time units against a
// limit of 71. The x-to-0 assignment at time 0 is an `x0`, which is neither
// `01` nor `10`, so it neither opens a pulse nor closes one.
TEST(EdgeControlSpecifierEvaluation, WidthEdge01ClosesOnAOneToZeroTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $width(edge[01] clk, 71, 0);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    #191 clk = 1'b1;\n"
      "    #3 clk = 1'b0;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "$width violation: signal",
                              LineHolding(kDesign, "$width(edge[01] clk"),
                              "31.4.4"));
}

// §31.4.4 with the same design and the same limit as the case above, the value
// the clock leaves the pulse for alone changed: `clk` goes from 1 to x, and
// `1x` is not the reverse of `01`, so no data event closes the pulse and
// nothing is reported. The pulse is 4 time units wide against a limit of 71, so
// a driver that closed the pulse on any transition would report; `clk` rises at
// time 211 and reaches x at time 215.
TEST(EdgeControlSpecifierEvaluation, WidthEdge01IgnoresAOneToXTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top;\n"
      "  logic clk;\n"
      "  specify\n"
      "    $width(edge[01] clk, 71, 0);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    #211 clk = 1'b1;\n"
      "    #4 clk = 1'bx;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$width violation: signal"), nullptr);
}

}  // namespace
