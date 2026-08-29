// §30.4.4's condition as §30.5.3's selection reads it, taken off a running
// simulation: a design carrying the subclause's own Example 2 is driven once
// per value of MODE, and the time `y` moved says which of the five
// state-dependent paths were active when the delay was chosen.
//
// §30.5.3 makes the condition half of what active means. "Active specify paths
// are those whose input has transitioned most recently in time, and either
// they have no condition or their conditions are true." Only the
// transition-time half was applied, so a state-dependent path was active
// whatever its condition said and the smallest delay of all five always won.
// Issue #3389 is that gap.
//
// Neither file beside this one can fail on it.
// test/src/unit/test_simulator_subclause_30_05_03a.cpp calls SelectPathDelay
// from src/simulator/specify_path_delay.h itself and hands it the
// PathCandidate::condition_true flags as arguments, so it proves the
// comparison that reads those flags and says nothing about whether anything
// computes one from a condition.
// test/src/unit/test_simulator_subclause_30_05_03b.cpp does drive a design,
// but the Example 1 paths it drives carry no condition at all, so every
// candidate it builds is active on the transition time alone.
//
// Example 2 is the design under the first three cases:
//
//     if (MODE < 5) (A => Y) = (5, 9);
//     if (MODE < 4) (A => Y) = (4, 8);
//     if (MODE < 3) (A => Y) = (6, 5);
//     if (MODE < 2) (A => Y) = (3, 2);
//     if (MODE < 1) (A => Y) = (7, 7);
//
// and the clause's prose about it is what the first two cases assert.
// "Anywhere from zero to five of these specify paths might be active depending
// upon the value of MODE. For instance, when MODE is 2, the first three
// specify paths are active. A rise transition would select a delay of 4
// because that is the smallest rise delay among the first three."
//
// The delays are the standard's own, and each case tells apart quantities that
// share no value. At MODE 2 the answer is a rise delay of 4 and the answer a
// run ignoring the conditions gives is 3, the smallest rise delay of all five;
// they differ by a single time unit, which is why every case reads the time
// `y` moved off an `always @(y)` rather than off a sample. At MODE 0 the
// answer is that same 3, so the first two cases differ in one parameter value
// and in nothing else, and that pair is what says the condition is being read
// rather than one answer being given to both. At MODE 2 the answer 4 is also
// apart from the 5 that the fall slot of Table 30-2 holds for the same three
// paths, so a selection reading the wrong slot does not land on it either.
//
// At MODE 5 every condition is false and no specify path is active, which is
// the third case. §30.6 rules that where a module path delay and a distributed
// delay both reach an output "the larger of the two delays for each path shall
// be used", and with no active path there is no module path delay to be the
// larger: `assign y = a;` carries no delay of its own, so `y` follows `a` in
// the same time slot and the transition prints at the time the stimulus was
// written. That answer is 0 added time units, which is apart from all five of
// 3, 4, 5, 6 and 7 rather than from one of them.
//
// The fourth and fifth cases are §30.4.4.4's ifnone path beside one
// conditional path. "The ifnone keyword is used to specify a default
// state-dependent path delay when all other conditions for the path are
// false", so the conditional delay governs while `C` holds and the ifnone
// delay governs while it does not. Those are two claims and so two tests. The
// delays 13 and 21 are used for nothing else in this file, so neither case's
// answer is a value some other case could have produced.
//
// The stimulus is one rise at t=50 in every case, and the largest delay any
// case selects is 21, so `y` moves once and §30.7 has no second scheduled
// transition to deem a pulse.
//
// `a` is an input port and `y` an output port because §30.4.1 requires a
// module path source to be a net connected to an input or inout port and a
// destination to be connected to an output or inout port, and
// CheckSpecifyPathTerminal in src/elaborator/elaborator_validate_specify.cpp
// rejects a path terminal that is a declared local signal. An input port of a
// top module has no driver, so `sa` supplies one through `assign a = sa;`,
// which §23.3.3.3 admits onto a net input port and which costs a delta cycle
// and no simulation time. Every time below is therefore the time `sa` was
// written.
//
// MODE and C are parameters rather than variables because Lowerer::LowerParams
// in src/simulator/lowerer.cpp creates a SimContext variable for each
// parameter of a module, under the instance prefix that is empty for a top
// module. A condition naming one is therefore a name EvalExpr resolves at run
// time, and a case is one number in the source rather than an extra assignment
// the stimulus has to get out of the way before the edge under test.
//
// `armed` exists because `y` leaves its initial x somewhere in the first 21
// time units, at a moment the delays §30.5.2 derives for the x and z slots
// decide and no case here is about. It is raised at t=40, after that settling
// and before the one stimulus edge that matters, so the run prints one
// transition line and it belongs to the case.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §30.5.3's Example 2, with the standard's `A` and `Y` written as the design's
// own port names and `MODE` left to the parameter the case fixes.
constexpr std::string_view kExample2Paths =
    "    if (MODE < 5) (a => y) = (5, 9);\n"
    "    if (MODE < 4) (a => y) = (4, 8);\n"
    "    if (MODE < 3) (a => y) = (6, 5);\n"
    "    if (MODE < 2) (a => y) = (3, 2);\n"
    "    if (MODE < 1) (a => y) = (7, 7);\n";

// §30.4.4.4's pairing: one conditional path and the ifnone path that answers
// for the same two terminals when the condition is false. A single delay
// value fills all twelve transition slots per §30.5.1, so which of the two
// governed is one number whichever transition is scheduled.
constexpr std::string_view kIfnonePaths =
    "    if (C) (a => y) = 13;\n"
    "    ifnone (a => y) = 21;\n";

// The stimulus and the three things every case reads. `sa` rises once, at
// t=50; the `always @(y)` names the time `y` followed it, which is the answer
// each case asserts; and the two samples straddle every delay any case could
// select, so the transition line is corroborated by `y` having been 0 before
// t=50 and 1 well after it. Neither sample time is one a case's edge can land
// on, so no sample reads a value in the time slot it is being written.
constexpr std::string_view kStimulusAndProbes =
    "  always @(y) begin\n"
    "    if (armed) $display(\"edge %b at %0d\", y, $time);\n"
    "  end\n"
    "  initial begin\n"
    "    armed = 1'b0;\n"
    "    sa = 1'b0;\n"
    "    #40 armed = 1'b1;\n"
    "    #10 sa = 1'b1;\n"
    "  end\n"
    "  initial #45 $display(\"at 45 y=%b\", y);\n"
    "  initial #80 $display(\"at 80 y=%b\", y);\n"
    "endmodule\n";

// A design whose single module path source is `a`, carrying `paths` inside its
// specify block and one parameter declared as `param` spells it.
//
// The module is the only one in the source and so the one ElaborateSrc
// elaborates, and it is a top module because only a top module's specify block
// is registered, which issue #3383 records.
std::string PathSource(const std::string& param, std::string_view paths) {
  std::string src = "module dut #(parameter " + param + ")";
  src += " (input a, output y);\n";
  src += "  logic sa, armed;\n";
  src += "  assign a = sa;\n";
  src += "  assign y = a;\n";
  src += "  specify\n";
  src.append(paths);
  src += "  endspecify\n";
  src.append(kStimulusAndProbes);
  return src;
}

// §30.5.3: "when MODE is 2, the first three specify paths are active. A rise
// transition would select a delay of 4 because that is the smallest rise delay
// among the first three." `MODE < 2` and `MODE < 1` are false, so the paths
// carrying the rise delays 3 and 7 are not among the candidates the comparison
// runs over, and `y` reaches 1 at t=54. A run that took every path reaching
// `y` as active would answer 3 and place the edge at t=53.
TEST(StateDependentPathActivity, FalseConditionsWithholdTheSmallerRiseDelay) {
  SimFixture f;
  std::string out = RunCapture(PathSource("MODE = 2", kExample2Paths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 54\nat 80 y=1\n");
}

// §30.5.3 puts "anywhere from zero to five of these specify paths" in play, and
// at MODE 0 all five conditions are true. Every path is active, so the
// comparison runs over the rise delays 5, 4, 6, 3 and 7 and settles on 3,
// placing `y` at 1 at t=53. The design differs from the case above in the
// value of MODE alone, so the two answers differing is the condition being
// read.
TEST(StateDependentPathActivity, EveryTrueConditionLeavesEveryPathActive) {
  SimFixture f;
  std::string out = RunCapture(PathSource("MODE = 0", kExample2Paths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 53\nat 80 y=1\n");
}

// §30.5.3 allows that zero of the five paths may be active, and MODE 5 is the
// value that makes it so: `MODE < 5` is false and so is every condition below
// it. No module path delay governs the transition, and §30.6's larger of the
// module path delay and the distributed delay is then the distributed delay
// alone, which `assign y = a;` leaves at zero. `y` therefore follows `a` in
// the time slot `sa` was written in and the edge prints at t=50 -- not at any
// of the 53, 54, 55, 56 and 57 that the five rise delays would give.
TEST(StateDependentPathActivity, NoTrueConditionLeavesNoPathActive) {
  SimFixture f;
  std::string out = RunCapture(PathSource("MODE = 5", kExample2Paths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 50\nat 80 y=1\n");
}

// §30.4.4.4: the ifnone path states "a default state-dependent path delay when
// all other conditions for the path are false". With C at 1 the condition of
// the companion path is true, so that path is the active one and its delay of
// 13 places `y` at 1 at t=63. The ifnone delay of 21 would have placed it at
// t=71.
TEST(StateDependentPathActivity, TrueConditionOutranksTheIfnonePath) {
  SimFixture f;
  std::string out = RunCapture(PathSource("C = 1", kIfnonePaths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 63\nat 80 y=1\n");
}

// §30.4.4.4, the other half of the same sentence: with C at 0 the only other
// condition for the path is false, so the ifnone path is what remains active
// and its delay of 21 places `y` at 1 at t=71. The design differs from the
// case above in the value of C alone.
TEST(StateDependentPathActivity, IfnonePathGovernsWhenTheConditionIsFalse) {
  SimFixture f;
  std::string out = RunCapture(PathSource("C = 0", kIfnonePaths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 71\nat 80 y=1\n");
}

}  // namespace
