#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
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

}  // namespace
