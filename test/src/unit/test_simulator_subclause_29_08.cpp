#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §29.8 "UDP instances" is what puts a user-defined primitive into a design:
// "Instances of UDPs are specified inside modules in the same manner as gates
// (see 28.3)". Every case here therefore runs a whole design -- elaborate,
// lower, run -- and reads the value the run left on the net the instance's
// output terminal names.
//
// Constructing a UdpEvalState (src/simulator/udp_eval.h) from a UdpDecl and
// handing it an input vector, the way
// test/src/unit/test_simulator_subclause_29_05.cpp does for §29.5's table
// rules, would cover the state table and not the instance.
//
// An instance that elaborates to nothing leaves its output terminal with no
// driver, and SimContext::CreateNet (src/simulator/sim_context.cpp:306) leaves
// an ordinary net at z until a driver reaches it. So every expectation below
// names '0', '1' or 'x', none of which an undriven net can produce.

// A combinational primitive under §29.4: one field per input, one output field,
// no current-state field and no reg output. Every combination of 0 and 1 on the
// two inputs selects a row, so a run that drives both inputs to a known value
// never reaches §29.3.4's default output state.
constexpr const char* kAndPrimitive =
    "primitive udp_and (y, a, b);\n"
    "  output y;\n"
    "  input a, b;\n"
    "  table\n"
    "  // a b : y\n"
    "    1 1 : 1 ;\n"
    "    0 ? : 0 ;\n"
    "    ? 0 : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

// A combinational primitive whose table names two of the four combinations of 0
// and 1 on its inputs, so a run driving (1, 1) reaches §29.3.4's default: "All
// combinations of input values that are not explicitly specified result in a
// default output state of x."
constexpr const char* kPartialPrimitive =
    "primitive udp_partial (y, a, b);\n"
    "  output y;\n"
    "  input a, b;\n"
    "  table\n"
    "  // a b : y\n"
    "    0 0 : 0 ;\n"
    "    0 1 : 1 ;\n"
    "  endtable\n"
    "endprimitive\n";

// §29.5's latch, whose output q is declared reg under §29.3.2 and whose table
// carries the current-state field §29.5 adds: "The output value of the UDP is
// always the same as the internal state." The `-` in the third row is §29.3.6's
// no-change symbol, so an evaluation with ena_ high leaves the state where the
// previous evaluation put it.
constexpr const char* kLatchPrimitive =
    "primitive udp_latch (q, ena_, data);\n"
    "  output q; reg q;\n"
    "  input ena_, data;\n"
    "  table\n"
    "  // ena_ data : q : q+\n"
    "    0 1 : ? : 1 ;\n"
    "    0 0 : ? : 0 ;\n"
    "    1 ? : ? : - ;\n"
    "  endtable\n"
    "endprimitive\n";

// The design a combinational case runs: `primitive` as written, then a module
// declaring the two input terminals as reg and the output terminal as wire,
// `instantiation` written verbatim as the module's only logic, and an initial
// block driving the inputs to `a` and `b` at time zero.
std::string InstanceDesign(const char* primitive, const char* instantiation,
                           const char* a, const char* b) {
  return std::string(primitive) +
         "module m;\n"
         "  reg a, b;\n"
         "  wire y;\n"
         "  " +
         instantiation + "\n  initial begin a = " + a + "; b = " + b +
         "; end\n"
         "endmodule\n";
}

// Elaborates, lowers and runs `src`, then returns what the run left on `name`,
// one character per bit through Logic4Vec::ToString (src/common/types.cpp:70):
// '0', '1', 'x' or 'z'. A source that does not elaborate returns "<no-design>"
// and a run that declared no such signal returns "<no-signal>", so neither is
// read as a driven value.
std::string SettledValue(const std::string& src, const char* name) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return "<no-design>";
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr);
  return var == nullptr ? "<no-signal>" : var->value.ToString();
}

// §29.8: an instance of a primitive drives the net its output terminal names,
// with the value §29.4's table gives for the values on its input terminals. The
// two runs drive the same instance to opposite rows, so the expectation is not
// satisfied by any one constant: an instance that drove nothing would leave y
// at z in both, and an instance stuck on one row would fail the other.
TEST(UdpInstanceSim, CombinationalInstanceDrivesOutputTerminalFromTable) {
  EXPECT_EQ(SettledValue(InstanceDesign(kAndPrimitive, "udp_and g (y, a, b);",
                                        "1'b1", "1'b1"),
                         "y"),
            "1");
  EXPECT_EQ(SettledValue(InstanceDesign(kAndPrimitive, "udp_and g (y, a, b);",
                                        "1'b0", "1'b1"),
                         "y"),
            "0");
}

// §29.3.4: "All combinations of input values that are not explicitly specified
// result in a default output state of x." udp_partial names no row for (1, 1),
// so an instance driven there drives x. The first run drives (0, 1), which one
// row does name, and it is what separates the default from an output terminal
// nobody drives: a net with no driver settles at z, so a run reporting '1' for
// one combination and 'x' for the other reports the primitive's own default.
TEST(UdpInstanceSim, UnspecifiedInputCombinationDrivesUnknown) {
  EXPECT_EQ(
      SettledValue(InstanceDesign(kPartialPrimitive, "udp_partial g (y, a, b);",
                                  "1'b0", "1'b1"),
                   "y"),
      "1");
  EXPECT_EQ(
      SettledValue(InstanceDesign(kPartialPrimitive, "udp_partial g (y, a, b);",
                                  "1'b1", "1'b1"),
                   "y"),
      "x");
}

// §29.8: the `delay2` written on a primitive instance is the propagation delay
// from an input terminal to the output terminal -- "Only two delays may be
// specified because z is not supported for UDPs" -- and where the source writes
// one value §28.16 rules that "this value shall be used for all propagation
// delays". The inputs reach (0, 1) at time 100, which selects the row driving
// 0, and (1, 1) at time 200, which selects the row driving 1. So the output
// terminal changes from 0 to 1 at time 205.
//
// The two samples straddle that time rather than landing on it. A sample taken
// at time 205 would read the net in the same time slot as the delayed update
// writes it, and §4.7 rules that "active events can be taken off the Active or
// Reactive event region and processed in any order", so which of the two values
// it read would not be decided by §29.8. Time 204 is four time units after the
// input change, where a delay dropped between the parser and the run would
// already show 1, and time 206 is past the point where the delay has elapsed.
//
// The value read at time 204 is put there by the transition at time 100 rather
// than by the values the initial block writes at time 0. A primitive instance
// carrying a delay spends the first delay suspended, so whether it observes an
// input written in the time slot it starts in depends on the order the
// scheduler resumes it and the initial block in, which §4.7 leaves open.
TEST(UdpInstanceSim, DelayOnInstanceHoldsOutputTerminalAtItsOldValue) {
  SimFixture f;
  std::string src = std::string(kAndPrimitive) +
                    "module m;\n"
                    "  reg a, b;\n"
                    "  reg early, late;\n"
                    "  wire y;\n"
                    "  udp_and #5 g (y, a, b);\n"
                    "  initial begin\n"
                    "    a = 1'b0; b = 1'b0;\n"
                    "    #100 b = 1'b1;\n"
                    "    #100 a = 1'b1;\n"
                    "  end\n"
                    "  initial begin #204 early = y; #2 late = y; end\n"
                    "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* early = f.ctx.FindVariable("early");
  auto* late = f.ctx.FindVariable("late");
  ASSERT_NE(early, nullptr);
  ASSERT_NE(late, nullptr);
  EXPECT_EQ(early->value.ToString(), "0");
  EXPECT_EQ(late->value.ToString(), "1");
}

// §29.8: the delay written on the instance is the one charged, not merely some
// delay. This design's only event after the input change at time 10 is the
// output terminal taking the table's value, so the time the scheduler stops at
// is the input-change time plus the instance's delay. Landing at 15 fails both
// for a delay dropped between Parser::ParseUdpInstList (src/parser/
// parser_udp.cpp:17) and the run, which would stop at 10, and for a delay
// charged at any other number of ticks.
TEST(UdpInstanceSim, DelayOnInstanceIsChargedAtTheTicksWritten) {
  SimFixture f;
  auto* design = ElaborateSrc(
      std::string(kAndPrimitive) +
          "module m;\n"
          "  reg a, b;\n"
          "  wire y;\n"
          "  udp_and #5 g (y, a, b);\n"
          "  initial begin a = 1'b0; b = 1'b0; #10 a = 1'b1; b = 1'b1; end\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 15u);
}

// §29.5: a primitive whose output is declared reg holds an internal state
// between evaluations, and "The output value of the UDP is always the same as
// the internal state." One instance therefore keeps one state for the whole
// run.
//
// The run drives two evaluations after the terminals have settled. At time 10
// ena_ goes low with data high, which selects `0 1 : ? : 1` and puts the state
// at 1. At time 20 ena_ goes high and data low, which selects `1 ? : ? : -` and
// holds. The expected 1 is reached only by a state carried across the two: an
// instance that built a fresh UdpEvalState per event would enter the second
// evaluation with an unknown output, this primitive carrying no §29.3.3 initial
// statement, and the `-` Table 29-1 of §29.3.6 reads as "No change" would
// resolve against that unknown and drive x.
//
// The terminals settle at time 0 and the first evaluation under test is at time
// 10, because §4.7 leaves open whether the instance or the initial block runs
// first in the time slot they both start in.
TEST(UdpInstanceSim, SequentialInstanceKeepsOneStateForTheRun) {
  EXPECT_EQ(SettledValue(std::string(kLatchPrimitive) +
                             "module m;\n"
                             "  reg ena_, data;\n"
                             "  wire q;\n"
                             "  udp_latch g (q, ena_, data);\n"
                             "  initial begin\n"
                             "    ena_ = 1'b1; data = 1'b0;\n"
                             "    #10 ena_ = 1'b0; data = 1'b1;\n"
                             "    #10 ena_ = 1'b1; data = 1'b0;\n"
                             "  end\n"
                             "endmodule\n",
                         "q"),
            "1");
}

// §29.8: "An optional range may be specified for an array of UDP instances",
// and "The terminal connection rules remain the same as outlined in 28.3.6".
// `udp_and g [3:0] (y, a, b)` is therefore four instances of udp_and, and
// §28.3.6 connects element p to bit p of every terminal whose width is the
// array length while broadcasting a single-bit terminal to all four.
//
// The first run drives a and b to different values on different bits. Its
// expected 1000 is reached only by four evaluations of the table, each on one
// element's own input bits: an instance array that elaborates to nothing leaves
// y at zzzz, one evaluation over the whole vector drives the four output bits
// from a single table row rather than from four, and an expansion pairing
// element p with bit 3-p of one terminal drives 0001.
//
// The second run holds b at one bit, which §28.3.6 broadcasts, so y takes a
// unchanged. Its 1100 differs from the first run's 1000, so no one constant
// satisfies both.
//
// Both values are read after Scheduler::Run has returned, which is strictly
// after every event this design schedules, so §4.7's rule that active events
// "can be taken off the Active or Reactive event region and processed in any
// order" does not decide what is read.
TEST(UdpInstanceSim, InstanceArrayDrivesEachOutputBitFromItsOwnElement) {
  EXPECT_EQ(SettledValue(std::string(kAndPrimitive) +
                             "module m;\n"
                             "  reg [3:0] a, b;\n"
                             "  wire [3:0] y;\n"
                             "  udp_and g [3:0] (y, a, b);\n"
                             "  initial begin a = 4'b1100; b = 4'b1010; end\n"
                             "endmodule\n",
                         "y"),
            "1000");
  EXPECT_EQ(SettledValue(std::string(kAndPrimitive) +
                             "module m;\n"
                             "  reg [3:0] a;\n"
                             "  reg b;\n"
                             "  wire [3:0] y;\n"
                             "  udp_and g [3:0] (y, a, b);\n"
                             "  initial begin a = 4'b1100; b = 1'b1; end\n"
                             "endmodule\n",
                         "y"),
            "1100");
}

}  // namespace
