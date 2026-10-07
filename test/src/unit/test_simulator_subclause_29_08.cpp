#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §29.8 "UDP instances" is what puts a user-defined primitive into a design:
// UDP instances are written inside modules as gates are (§28.3). Every case
// here therefore runs a whole design -- elaborate, lower, run -- and reads the
// value the run left on the net the instance's output terminal names.
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
// and 1 on its inputs, so a run driving (1, 1) reaches §29.3.4's default, under
// which any input combination the table does not list gives the output x.
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
// carries the current-state field §29.5 adds, the UDP's output always equalling
// its internal state. The `-` in the third row is §29.3.6's no-change symbol,
// so an evaluation with ena_ high leaves the state where the previous
// evaluation put it.
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

// §29.3.4: any input combination the table does not list gives the output x by
// default. udp_partial names no row for (1, 1), so an instance driven there
// drives x. The first run drives (0, 1), which one row does name, and it is
// what separates the default from an output terminal nobody drives: a net with
// no driver settles at z, so a run reporting '1' for one combination and 'x'
// for the other reports the primitive's own default.
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
// from an input terminal to the output terminal -- at most two, a UDP having no
// z -- and where the source writes one value §28.16 makes it the delay of every
// propagation. The inputs reach (0, 1) at time 100, which selects the row
// driving 0, and (1, 1) at time 200, which selects the row driving 1. So the
// output terminal changes from 0 to 1 at time 205.
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
// between evaluations, and its output always equals that state. One instance
// therefore keeps one state for the whole run.
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

// §29.8: an array of UDP instances may carry a range, and a UDP instance
// connects its terminals by §28.3.6's rules. `udp_and g [3:0] (y, a, b)` is
// therefore four instances of udp_and, and §28.3.6 connects element p to bit p
// of every terminal whose width is the array length while broadcasting a
// single-bit terminal to all four.
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

// §29.4 rules that a combinational UDP's output depends on its present inputs
// alone, and that each change of an input evaluates the UDP and sets the output
// to the value of the table row matching every input. The case above drives its
// inputs once and reads the value the single evaluation every element gets at
// time zero, so it holds whether or not a later change is ever seen. This one
// changes b alone at time 10 and asks for the row that change selects.
//
// a is held still across the change so that a watcher armed on a cannot carry
// the assertion: 1100 & 1010 is 1000 and 1100 & 0101 is 0100, so an element
// that stopped after its first evaluation reads 1000 here.
//
// §28.3.6, which §29.8 sends the terminal connection rules to, distributes both
// terminals bit by bit, so each element reads b[p] -- a select on a literal
// index, which is the only form InstanceArrayElementTerminals builds.
TEST(UdpInstanceSim,
     InstanceArrayReevaluatesOnALaterChangeOfADistributedInput) {
  EXPECT_EQ(SettledValue(std::string(kAndPrimitive) +
                             "module m;\n"
                             "  reg [3:0] a, b;\n"
                             "  wire [3:0] y;\n"
                             "  udp_and g [3:0] (y, a, b);\n"
                             "  initial begin\n"
                             "    a = 4'b1100; b = 4'b1010;\n"
                             "    #10 b = 4'b0101;\n"
                             "  end\n"
                             "endmodule\n",
                         "y"),
            "0100");
}

// The same rule where one terminal is broadcast rather than distributed.
// §28.3.6 gives every element the whole of a terminal whose width matches the
// single-instance port, so `enable` reaches each element as a plain identifier
// and a[p] as a bit-select.
//
// This is the half the case above cannot show. An element woken by the
// broadcast terminal re-reads its distributed one correctly, so a design whose
// later change writes the broadcast terminal is right whatever the bit-selects
// watch. Here the later change writes a alone, holding enable still, so the
// only name that can wake an element is the one that resolves to nothing:
// 1100 & 1 is 1100 and 0011 & 1 is 0011.
TEST(UdpInstanceSim,
     InstanceArrayWithABroadcastTerminalReevaluatesOnADistributedInput) {
  EXPECT_EQ(SettledValue(std::string(kAndPrimitive) +
                             "module m;\n"
                             "  reg [3:0] a;\n"
                             "  reg enable;\n"
                             "  wire [3:0] z;\n"
                             "  udp_and g [3:0] (z, a, enable);\n"
                             "  initial begin\n"
                             "    a = 4'b1100; enable = 1'b1;\n"
                             "    #10 a = 4'b0011;\n"
                             "  end\n"
                             "endmodule\n",
                         "z"),
            "0011");
}

// §29.8 (printed page 868): UDP instances are written inside modules as gates
// are, with up to two delays, and a module holding one is instantiated like any
// other (§23.3), so `and2 #1` inside `w` follows its inputs one unit late
// exactly as the same instance at the top does. The child's delayed instance
// never left its first value.
TEST(UdpInstanceDelayRun, DelayedUdpInsideAChildModuleFollowsItsInputs) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive and2 (y, a, b);\n"
                       "  output y;\n"
                       "  input a, b;\n"
                       "  table\n"
                       "    1 1 : 1 ;\n"
                       "    0 ? : 0 ;\n"
                       "    ? 0 : 0 ;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "module w (output o, input i1, i2);\n"
                       "  and2 #1 u(o, i1, i2);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  reg a = 0, b = 1; wire y, yt;\n"
                       "  w i(y, a, b);\n"
                       "  and2 #1 ut(yt, a, b);\n"
                       "  initial begin\n"
                       "    #5 $display(\"%b %b\", y, yt);\n"
                       "    a = 1; #3 $display(\"%b %b\", y, yt);\n"
                       "    b = 0; #3 $display(\"%b %b\", y, yt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 0\n1 1\n0 0\n");
}

// The same for a sequential UDP whose delay is the enclosing module's
// parameter: the stage built with `#(1)` moves q1 one unit after the clock, so
// the stage clocked by the same edge samples q1's old value. The delayed stage
// never updated.
TEST(UdpInstanceDelayRun, ParameterDelayedSequentialUdpInsideAStageUpdates) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("primitive dffi (q, clk, d);\n"
                 "  output q; reg q;\n"
                 "  input clk, d;\n"
                 "  initial q = 1'b1;\n"
                 "  table\n"
                 "    (01) 0 : ? : 0 ;\n"
                 "    (01) 1 : ? : 1 ;\n"
                 "    (0?) 1 : 1 : 1 ;\n"
                 "    (0?) 0 : 0 : 0 ;\n"
                 "    (?0) ? : ? : - ;\n"
                 "    ? (?"
                 "?) : ? : - ;\n"
                 "  endtable\n"
                 "endprimitive\n"
                 "module stage #(parameter D = 0) (output q, input clk, d);\n"
                 "  dffi #D u(q, clk, d);\n"
                 "endmodule\n"
                 "module top;\n"
                 "  reg clk = 0, d = 0; wire q1, q2;\n"
                 "  stage #(1) s1(q1, clk, d);\n"
                 "  stage #(0) s2(q2, clk, s1.q);\n"
                 "  initial begin\n"
                 "    #1 $display(\"%b %b\", q1, q2);\n"
                 "    clk = 1; #2 $display(\"%b %b\", q1, s2.q);\n"
                 "    clk = 0; #1 clk = 1; #2 $display(\"%b %b\", q1, q2);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 1\n0 1\n0 0\n");
}

// §29.6's `r 1 1 1 ? : ? : 1` row gives q = 1 on a rising clock with data 1,
// whatever the notifier input holds, `?` matching its x. An unnamed sequential
// instance inside a child module, its output on the module's output port,
// captured x instead where the same instance at the top captured 1.
TEST(UdpInstanceRun, UnnamedSequentialUdpInsideAChildModuleCaptures) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive posdff_udp(q, clock, data, preset, clear, "
                       "notifier);\n"
                       "  output q; reg q;\n"
                       "  input clock, data, preset, clear, notifier;\n"
                       "  table\n"
                       "    r 0 1 1 ? : ? : 0 ;\n"
                       "    r 1 1 1 ? : ? : 1 ;\n"
                       "    n ? ? ? ? : ? : - ;\n"
                       "    ? * ? ? ? : ? : - ;\n"
                       "    ? ? ? ? * : ? : x ;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "module dff(q, clock, data);\n"
                       "  output q; input clock, data;\n"
                       "  reg notifier;\n"
                       "  posdff_udp(q, clock, data, 1'b1, 1'b1, notifier);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  reg clock = 0, data = 0;\n"
                       "  wire q;\n"
                       "  dff u(.q(q), .clock(clock), .data(data));\n"
                       "  initial begin\n"
                       "    #20 data = 1; #20 clock = 1;\n"
                       "    #1 $display(\"%b %b\", u.notifier, q);\n"
                       "    #9 clock = 0; #10 data = 0; #10 clock = 1;\n"
                       "    #1 $display(\"%b %b\", u.notifier, q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "x 1\nx 0\n");
}

}  // namespace
