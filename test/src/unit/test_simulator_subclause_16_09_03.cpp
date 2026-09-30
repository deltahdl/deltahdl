#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/assertion.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(Assertion, ChangedDetected) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_changed";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_changed", 5);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_changed"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_changed", 7);
  EXPECT_EQ(r1, AssertionResult::kPass);
}

TEST(Assertion, ChangedStable) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_changed2";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_changed2", 42);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_changed2"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_changed2", 42);
  EXPECT_EQ(r1, AssertionResult::kFail);
}

// §16.9.3: $rose returns true if the LSB of the expression changed to 1.
TEST(Assertion, RoseDetectsLowToHigh) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose", 1), AssertionResult::kPass);
}

// §16.9.3: $rose returns false when the LSB did not change to 1.
TEST(Assertion, RoseFalseWhenAlreadyHigh) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose2";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose2", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose2"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose2", 1), AssertionResult::kFail);
}

// §16.9.3: $fell returns true if the LSB of the expression changed to 0.
TEST(Assertion, FellDetectsHighToLow) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell", 0), AssertionResult::kPass);
}

// §16.9.3: $fell returns false when the LSB did not change to 0.
TEST(Assertion, FellFalseWhenNotFalling) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell2";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell2", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell2"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell2", 0), AssertionResult::kFail);
}

// §16.9.3 ($rose negative form): a falling LSB is not a rise, so $rose returns
// false when the LSB changes from 1 to 0.
TEST(Assertion, RoseFalseWhenLsbFalls) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose3";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose3", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose3"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose3", 0), AssertionResult::kFail);
}

// §16.9.3 ($rose is LSB-only): $rose watches only the least significant bit. A
// change confined to the higher bits (2'b00 -> 2'b10) does not raise the LSB,
// so $rose is false even though the value changed. This is the distinction from
// $changed, which observes the whole value.
TEST(Assertion, RoseIgnoresHigherBitsWhenLsbUnchanged) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose4";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose4", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose4"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose4", 2), AssertionResult::kFail);
}

// §16.9.3 ($fell negative form): a rising LSB is not a fall, so $fell returns
// false when the LSB changes from 0 to 1.
TEST(Assertion, FellFalseWhenLsbRises) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell3";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell3", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell3"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell3", 1), AssertionResult::kFail);
}

// §16.9.3 ($fell is LSB-only): a change confined to the higher bits
// (2'b01 -> 2'b11) leaves the LSB at 1, so $fell is false even though the value
// changed — the counterpart of the $rose LSB-only case.
TEST(Assertion, FellIgnoresHigherBitsWhenLsbUnchanged) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell4";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell4", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell4"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell4", 3), AssertionResult::kFail);
}

// §16.9.3: $stable returns true if the value of the expression did not change.
TEST(Assertion, StableTrueWhenUnchanged) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_stable";
  prop.kind = SvaPropertyKind::kStable;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_stable", 9);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_stable"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_stable", 9), AssertionResult::kPass);
  EXPECT_EQ(monitor.Evaluate("p_stable", 4), AssertionResult::kFail);
}

// §16.9.3: when a value change function is called at or before the first
// clocking event, there is no prior real sample to compare against; the first
// evaluation seeds the sampled value rather than reporting a change.
TEST(Assertion, FirstEvaluationHasNoPriorSample) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_first";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  EXPECT_EQ(monitor.Evaluate("p_first", 5), AssertionResult::kVacuousPass);
}

// §16.9.3: "$sampled returns the sampled value of its argument (see 16.5.1)",
// and §16.5.1 makes that "the value of this variable in the Preponed region of
// this time slot" -- the value it held before anything in this slot wrote it.
// The function returned EvalExpr of its argument, which is the live value, so
// the two coincided only where nothing had changed and $sampled was an identity
// everywhere else.
//
// The write and the read stand in one time slot here, which is the only shape
// that tells the two apart: 8'h11 is what the slot began with and 8'h22 is what
// the live variable holds when the read runs.
TEST(SampledValueSim, SampledReadsThePreponedValueOfItsArgument) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  reg [7:0] x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 8'h11;\n"
      "    #10;\n"
      "    x = 8'h22;\n"
      "    result = $sampled(x);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x11u);
}

// §16.9.3: "$rose returns true (1'b1) if the LSB of the expression changed to
// 1", compared against "the sampled value of the expression from the most
// recent strictly prior time step in which the clocking event occurred" -- and
// where no such step has occurred, against the default sampled value, which
// §16.5.1 makes the value the declaration assigned. `req` is declared 0 and is
// 1 at the first edge, so it rose and the property holds.
//
// $rose returned a constant zero, so this property was false at every tick and
// an assertion written on it could not pass.
TEST(SampledValueSim, RoseHoldsWhenTheLsbRisesBeforeTheEdge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic req = 0;\n"
      "  always @(posedge clk) assert property ($rose(req));\n"
      "  initial begin\n"
      "    #1 req = 1;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "");
}

// The other half of the pair, which is what separates a working $rose from one
// answering true for everything: `req` never leaves 0, so nothing rose and the
// property fails.
TEST(SampledValueSim, RoseFailsWhenTheLsbDoesNotRise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic req = 0;\n"
      "  always @(posedge clk) assert property ($rose(req));\n"
      "  initial #1 clk = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

// §16.9.3 gives $past "the value of b sampled at the previous occurrence of
// (posedge clk)", the default number_of_ticks being 1. It returned the current
// value, so `x != $past(x)` was never true and a property watching for a change
// could not fire.
//
// The recorded value is read rather than an assertion's verdict, so what the
// case asserts is the value the clause names: x is 1 at the first edge and 2 at
// the second, so the second edge's $past is 1.
TEST(SampledValueSim, PastReturnsTheValueSampledAtThePreviousTick) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int x = 1;\n"
      "  int seen = 99;\n"
      "  always @(posedge clk) seen = $past(x);\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0;\n"
      "    x = 2;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §16.9.3: `$past(expression1, number_of_ticks)` returns the value sampled
// number_of_ticks ticks back, so at the third edge `$past(x, 2)` is the 1 of
// the first while `$past(x)` is the 2 of the second.
TEST(SampledValueSim, PastLooksBackTheStatedNumberOfTicks) {
  SimFixture f;
  auto* two_back = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int x = 1;\n"
      "  int two_back = 99;\n"
      "  int one_back = 99;\n"
      "  always @(posedge clk) begin\n"
      "    two_back = $past(x, 2);\n"
      "    one_back = $past(x);\n"
      "  end\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; x = 2;\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; x = 3;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "two_back");
  ASSERT_NE(two_back, nullptr);
  EXPECT_EQ(two_back->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("one_back")->value.ToUint64(), 2u);
}

// §16.9.3: `expression2` gates the clocking event of $past, the sampling of
// expression1 being on `posedge clk iff enable`, so ticks at which enable is
// low are neither recorded nor counted: with q written 1, 2 and 3 at the
// three edges and enable low at the second, `$past(q, 1, enable)` at the
// third edge is the 1 of the first and not the 2 of the second.
TEST(SampledValueSim, PastGatedByExpression2SkipsTheTicksItIsLowAt) {
  SimFixture f;
  auto* seen = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic enable = 1;\n"
      "  int q = 1;\n"
      "  int seen = 99;\n"
      "  always @(posedge clk) seen = $past(q, 1, enable);\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; q = 2; enable = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; q = 3; enable = 1;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 1u);
}

// §16.9.3: $past may refer to automatic variables, its example reading
// `$past(b[i])` in a for loop over i and returning at each iteration the past
// value of the i-th bit. b is 4'b0101 at the first edge and 4'b1010 at the
// second, so at the second edge the loop copies the first edge's bits, 0101,
// into r; one history for the whole call site would hand every iteration the
// last value it saw.
TEST(SampledValueSim, PastOfAnIndexedBitInALoopReadsThatBitsPast) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [3:0] b = 4'b0101;\n"
      "  logic [3:0] r = 4'b1111;\n"
      "  always @(posedge clk)\n"
      "    for (int i = 0; i < 4; i++) r[i] = $past(b[i]);\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; b = 4'b1010;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0b0101u);
}

// §16.9.3 (printed pages 415 and 417) and §20.12: a value change function
// given a clocking event compares the sampled value of its argument now with
// the one at the most recent strictly prior tick of that event. s is set to 1
// at the rise of 5 and read one time unit after the rise of 15, where it was
// already 1, and set to 0 at the rise of 25 and read after the rise of 35,
// where it was already 0, so neither call sees a change.
TEST(SampledValueExplicitClock, ProceduralValueChangeComparesTheClocksTicks) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic s = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin\n"
      "    @(posedge clk); s = 1;\n"
      "    @(posedge clk); #1;\n"
      "    $display(\"OUT rose %0d fell %0d\", $rose(s, @(posedge clk)), "
      "$fell(s, @(posedge clk)));\n"
      "    @(posedge clk); s = 0;\n"
      "    @(posedge clk); #1;\n"
      "    $display(\"OUT rose %0d fell %0d\", $rose(s, @(posedge clk)), "
      "$fell(s, @(posedge clk)));\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "OUT rose 0 fell 0\nOUT rose 0 fell 0\n");
}

// The same with $fell called first and $stable after it: s falls at the rise
// of 5 and is read after the rise of 15, where it was already 0, so $fell and
// $rose are 0 and $stable 1, whichever call the process makes first.
TEST(SampledValueExplicitClock, ProceduralFellStableAndRoseAgree) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic s = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin\n"
      "    @(posedge clk); s = 0;\n"
      "    @(posedge clk); #1;\n"
      "    $display(\"OUT fell %0d rose %0d stable %0d\", $fell(s, @(posedge "
      "clk)), $rose(s, @(posedge clk)), $stable(s, @(posedge clk)));\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "OUT fell 0 rose 0 stable 1\n");
}

// §16.9.3: in an assertion, a clocking event given to a sampled value function
// is the one its samples are taken at, whatever the assertion's own clock.
// req is high for the clk cycles from 15 and from 35; clk2 rises at 20, 40, 60
// and 80, so under posedge clk $rose(req) holds twice, and
// $rose(req, @(posedge clk2)), comparing req at clk2's ticks, holds once.
TEST(SampledValueExplicitClock, AnAssertionsFunctionSamplesAtItsOwnClock) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic clk2 = 0; initial begin #10; repeat (9) #10 clk2 = ~clk2; end\n"
      "  bit [0:9] rv = 10'b0101000000;\n"
      "  bit req; assign req = rv[0];\n"
      "  always @(negedge clk) rv <= rv << 1;\n"
      "  int c1 = 0, c2 = 0;\n"
      "  cover property (@(posedge clk) $rose(req)) c1++;\n"
      "  cover property (@(posedge clk) $rose(req, @(posedge clk2))) c2++;\n"
      "  initial #98 $display(\"c1=%0d c2=%0d\", c1, c2);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "c1=2 c2=1\n");
}

// The prior point is the clocking event's tick and not the call's previous
// evaluation. One call site, evaluated twice by the loop, reads s after it
// rose and u after it fell since the last rise of clk, at 9 and at 19, and
// both times answers 1: at 19 the tick of 15 had sampled s at 0 and u at 1,
// where the evaluation at 9 had read s at 1 and u at 0.
TEST(SampledValueExplicitClock, ThePriorPointIsTheClocksTickNotTheLastCall) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  logic s = 0, u = 1;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 2; i++) begin\n"
      "      #8 s = 1; u = 0;\n"
      "      #1 $display(\"OUT rose %0d fell %0d\", $rose(s, @(posedge clk)), "
      "$fell(u, @(posedge clk)));\n"
      "      #1 s = 0; u = 1;\n"
      "    end\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "OUT rose 1 fell 1\nOUT rose 1 fell 1\n");
}

// The same for $changed and $stable: at 9 and at 19 s is 1 where the tick of
// 5, and then of 15, sampled it at 0, so $changed is 1 and $stable 0 both
// times, where comparing with the call's previous evaluation, which also read
// 1, would answer 0 and 1 the second time.
TEST(SampledValueExplicitClock, ChangedAndStableCompareTheClocksTick) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  logic s = 0;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 2; i++) begin\n"
      "      #8 s = 1;\n"
      "      #1 $display(\"OUT changed %0d stable %0d\", "
      "$changed(s, @(posedge clk)), $stable(s, @(posedge clk)));\n"
      "      #1 s = 0;\n"
      "    end\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "OUT changed 1 stable 0\nOUT changed 1 stable 0\n");
}

}  // namespace
