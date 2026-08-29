// §30.5.3's choice of a module path delay as a running simulation makes it: a
// design carrying the subclause's own Example 1 is driven, and the time `y`
// moved is read off what the run printed.
//
// §30.5.3 chooses in two steps. A simulator "shall do this by first determining
// which specify paths to the output are active. Active specify paths are those
// whose input has transitioned most recently in time", and only then "a delay
// shall be selected from among them ... by comparing the correct delay for the
// specific transition being scheduled from each specify path and choosing the
// smallest". The first step is the one
// test/src/unit/test_simulator_subclause_30_05_03a.cpp cannot make fail: that
// file calls SelectPathDelay from src/simulator/specify_path_delay.h itself and
// hands it the transition times as arguments, so it proves the arithmetic and
// says nothing about whether anything computes those times from a run. Issue
// #3385 is that gap. The delay was taken from every path reaching the output
// rather than from the active ones, and no test could tell, because none drove
// a design.
//
// Example 1 is the design under every case below:
//
//     (A => Y) = (6, 9);
//     (B => Y) = (5, 11);
//
// and the clause's prose about it is what the four cases assert. "For a Y
// transition from 0 to 1, if A transitioned more recently than B, a delay of 6
// will be chosen. But if B transitioned more recently than A, a delay of 5 will
// be chosen. And if, the last time they transitioned, A and B did so
// simultaneously, then the smallest of the two rise delays would be chosen,
// which is the rise delay from B of 5. The fall delay from A of 9 would be
// chosen if Y was instead to transition from 1 to 0."
//
// The delays are the standard's own and no two quantities a case tells apart
// share a value. 6 and 5 are the rise delays the first two cases tell apart;
// they differ by a single time unit, so no sample taken on a whole tick
// separates them, and the `always @(y)` below prints $time on every transition
// of `y` for exactly that reason. 9 and 11 are the fall delays the fourth case
// rests on, and 9 differs as well from the rise delay 6 that a selection
// reading the wrong slot of Table 30-2 would hand the same transition. The
// stimulus times 20, 40, 50 and 60 are spaced further apart than the largest
// delay 11, so no two transitions of `y` are ever close enough for §30.7 to
// deem them a pulse and filter one away.
//
// The expression driving `y` differs between the rise cases and the fall case,
// and each is chosen so that the input that transitioned most recently is the
// one that caused `y` to move. `a & b` rises when the later of the two inputs
// rises, and `a | b` falls when the later of the two falls; under the other
// operator the first input to move would carry `y` with it and the second could
// not be the cause of anything.
//
// `armed` exists because `y` settles out of its initial high-impedance value
// somewhere in the first eleven time units, at a moment the delays §30.5.2
// derives for the x and z slots decide and no case here is about. It is raised
// at t=40, after that settling and before every stimulus edge that matters, so
// the run prints one line per transition a case is making a claim about.
//
// `a` and `b` are input ports and `y` an output port because §30.4.1 requires a
// module path source to be a net connected to an input or inout port and a
// destination to be connected to an output or inout port, and
// CheckSpecifyPathTerminal in src/elaborator/elaborator_validate_specify.cpp
// rejects a path terminal that is a declared local signal. An input port of a
// top module has no driver, so `sa` and `sb` supply one through `assign a =
// sa;`, which §23.3.3.3 admits onto a net input port and which costs a delta
// cycle and no simulation time. Every time below is therefore the time `sa` or
// `sb` was written.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// One case's variables over Example 1's design: the expression that drives `y`,
// the statements the stimulus process runs after clearing `armed`, and the two
// times `y` is sampled at. The samples straddle the transition the case asserts
// and fall on no time any competing delay would place an edge at, so a sample
// never reads a value in the same time slot it is being written.
struct Example1Case {
  std::string_view driver;
  std::string_view stimulus;
  int early;
  int late;
};

// Example 1's two module paths over a driver of `y` the case chooses, with the
// case's stimulus reaching `a` and `b` through `sa` and `sb`.
//
// The module is the only one in the source and so the one ElaborateSrc
// elaborates, and it is a top module because only a top module's specify block
// is registered, which issue #3383 records. Each sample line names the time it
// was taken at, and each transition line names the time `y` moved, so a case
// asserts on times rather than on an order of values.
std::string Example1Source(const Example1Case& tc) {
  std::string early = std::to_string(tc.early);
  std::string late = std::to_string(tc.late);
  std::string src = "module top(input a, b, output y);\n";
  src += "  logic sa, sb, armed;\n";
  src += "  assign a = sa;\n";
  src += "  assign b = sb;\n";
  src += "  assign y = ";
  src += tc.driver;
  src += ";\n";
  src += "  specify\n";
  src += "    (a => y) = (6, 9);\n";
  src += "    (b => y) = (5, 11);\n";
  src += "  endspecify\n";
  src += "  initial begin\n";
  src += "    armed = 1'b0;\n";
  src += tc.stimulus;
  src += "  end\n";
  src += "  always @(y) begin\n";
  src += "    if (armed) $display(\"y=%b@%0d\", y, $time);\n";
  src += "  end\n";
  src += "  initial #" + early + " $display(\"s" + early + "=%b\", y);\n";
  src += "  initial #" + late + " $display(\"s" + late + "=%b\", y);\n";
  src += "endmodule\n";
  return src;
}

// §30.5.3: "if A transitioned more recently than B, a delay of 6 will be
// chosen". `b` rises at t=20 and `a` at t=50, and `a & b` holds `y` at 0 until
// the second of the two arrives, so the rise of `y` is caused by the input that
// transitioned most recently. Only the path from `a` is active, and its rise
// delay of 6 places `y` at 1 at t=56 -- not at the 55 that `b`'s rise delay of
// 5 would give, which is a whole time unit away and so the difference the
// printed transition time exists to state.
TEST(ActiveModulePathSelection, RiseTakesTheRiseDelayOfTheLaterInputA) {
  SimFixture f;
  std::string out = RunCapture(Example1Source({"a & b",
                                               "    sa = 1'b0;\n"
                                               "    sb = 1'b0;\n"
                                               "    #20 sb = 1'b1;\n"
                                               "    #20 armed = 1'b1;\n"
                                               "    #10 sa = 1'b1;\n",
                                               54, 58}),
                               f);
  EXPECT_EQ(out, "s54=0\ny=1@56\ns58=1\n");
}

// §30.5.3: "But if B transitioned more recently than A, a delay of 5 will be
// chosen". The same design and the same two transitions with their order
// exchanged -- `a` rises at t=20 and `b` at t=50 -- so what differs between
// this case and the one above is which input moved last and nothing else. The
// path from `b` is the active one and its rise delay of 5 places `y` at 1 at
// t=55. The pair is what says the delay follows the input that moved rather
// than sitting at either value.
TEST(ActiveModulePathSelection, RiseTakesTheRiseDelayOfTheLaterInputB) {
  SimFixture f;
  std::string out = RunCapture(Example1Source({"a & b",
                                               "    sa = 1'b0;\n"
                                               "    sb = 1'b0;\n"
                                               "    #20 sa = 1'b1;\n"
                                               "    #20 armed = 1'b1;\n"
                                               "    #10 sb = 1'b1;\n",
                                               54, 58}),
                               f);
  EXPECT_EQ(out, "s54=0\ny=1@55\ns58=1\n");
}

// §30.5.3: "if, the last time they transitioned, A and B did so
// simultaneously, then the smallest of the two rise delays would be chosen,
// which is the rise delay from B of 5". Both inputs rise at t=50, which leaves
// both paths active, so the comparison of the two rise delays is what settles
// the answer and `y` reaches 1 at t=55.
TEST(ActiveModulePathSelection, SimultaneousInputsRiseOnTheSmallerDelay) {
  SimFixture f;
  std::string out = RunCapture(Example1Source({"a & b",
                                               "    sa = 1'b0;\n"
                                               "    sb = 1'b0;\n"
                                               "    #40 armed = 1'b1;\n"
                                               "    #10 sa = 1'b1;\n"
                                               "    sb = 1'b1;\n",
                                               54, 58}),
                               f);
  EXPECT_EQ(out, "s54=0\ny=1@55\ns58=1\n");
}

// §30.5.3: "The fall delay from A of 9 would be chosen if Y was instead to
// transition from 1 to 0."
//
// Both inputs start at 1 and `a | b` holds `y` at 1 while either of them is
// still 1, which is what lets `b` fall at t=50 without moving `y` at all: the
// transition is recorded against `b` and nothing is scheduled for it. `a` then
// falls at t=60, `y` follows it down, and `a` is the input that transitioned
// most recently. That is the stimulus this case needs, because the standard's
// sentence is about a fall taken from the path whose input moved last.
//
// The active path is `a`'s and the transition being scheduled is a 1 to 0, so
// the delay is 9 and `y` reaches 0 at t=69. The two are selected independently:
// 11 is the fall delay of the other path and 6 the rise delay of this one, and
// neither places the edge at 69.
TEST(ActiveModulePathSelection, FallTakesTheFallDelayOfTheLaterInputA) {
  SimFixture f;
  std::string out = RunCapture(Example1Source({"a | b",
                                               "    sa = 1'b1;\n"
                                               "    sb = 1'b1;\n"
                                               "    #40 armed = 1'b1;\n"
                                               "    #10 sb = 1'b0;\n"
                                               "    #10 sa = 1'b0;\n",
                                               65, 73}),
                               f);
  EXPECT_EQ(out, "s65=1\ny=0@69\ns73=0\n");
}

}  // namespace
