#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

TEST(ConcurrentAssertionSampling, StaticVariableSamplesPreponedAtNonzeroTime) {
  SampledValue sv = SampleStaticVariable(0x1234, SimTime{10}, 0);
  EXPECT_EQ(sv.value, 0x1234u);
  EXPECT_EQ(sv.mode, SampleMode::kPreponed);
}

TEST(ConcurrentAssertionSampling, StaticVariableSamplesDefaultAtTimeZero) {
  SampledValue sv = SampleStaticVariable(0xDEAD, SimTime{0}, 0);
  EXPECT_EQ(sv.value, 0u);
  EXPECT_EQ(sv.mode, SampleMode::kDefault);
}

TEST(ConcurrentAssertionSampling, AutomaticVariableSamplesCurrentValue) {
  SampledValue sv = SampleAutomaticVariable(0xABCD);
  EXPECT_EQ(sv.value, 0xABCDu);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

// §16.5.1 / §16.10: a local variable is one of the exceptions to the Preponed
// sampling rule. Like an automatic variable, its sampled value is its current
// value, not a value read from the Preponed region. §16.10 states the same rule
// ("the sampled value of a local variable is the current value") and refers
// back to §16.5.1; SampleLocalVariable is the production carrier for that
// weave.
TEST(ConcurrentAssertionSampling, LocalVariableSamplesCurrentValue) {
  SampledValue sv = SampleLocalVariable(0x2468);
  EXPECT_EQ(sv.value, 0x2468u);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

// §16.5.1: the default sampled value of a static variable is the value assigned
// in its declaration, which is distinct from the plain uninitialized type
// default that any other variable/net gets. At time 0 the static variable
// therefore samples that declaration-assigned value (in kDefault mode) rather
// than its live/Preponed running value. The third argument models the value
// assigned in the declaration.
TEST(ConcurrentAssertionSampling,
     StaticVariableDefaultIsDeclarationAssignedValue) {
  SampledValue sv = SampleStaticVariable(0xDEAD, SimTime{0}, 7);
  EXPECT_EQ(sv.value, 7u);
  EXPECT_EQ(sv.mode, SampleMode::kDefault);
}

// §16.5.1: active free checker variables are the third kind, alongside
// automatic and local variables, that is excepted from Preponed sampling — its
// sampled value is its current value.
TEST(ConcurrentAssertionSampling,
     ActiveFreeCheckerVariableSamplesCurrentValue) {
  SampledValue sv = SampleActiveFreeCheckerVariable(0x1357);
  EXPECT_EQ(sv.value, 0x1357u);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

// §16.5.1: the current-value rule for a free checker variable has an exception
// — when a sampled value function ($past/$future) asks for a past or future
// value of an active free checker variable, that value comes from the Postponed
// region instead.
TEST(ConcurrentAssertionSampling, FreeCheckerPastFutureSamplesPostponedRegion) {
  SampledValue sv = SampleActiveFreeCheckerVarPastFuture(0x99);
  EXPECT_EQ(sv.value, 0x99u);
  EXPECT_EQ(sv.mode, SampleMode::kPostponed);
}

// §16.5.1: the complementary exception for automatic variables — a sampled
// value function's request for a past or future value of an automatic variable
// collapses to the automatic variable's current value rather than reaching into
// another clock tick.
TEST(ConcurrentAssertionSampling, AutomaticPastFutureCollapsesToCurrentValue) {
  SampledValue sv = SampleAutomaticVarPastFuture(0x42);
  EXPECT_EQ(sv.value, 0x42u);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, DefaultSampledValueOfTriggeredIsZero) {
  SampledValue t = DefaultSampledValueOfTriggered();
  EXPECT_EQ(t.value, 0u);
  SampledValue m = DefaultSampledValueOfMatched();
  EXPECT_EQ(m.value, 0u);
}

TEST(ConcurrentAssertionSampling,
     SingleVariableExpressionForwardsVariableSample) {
  SampledValue var = SampleStaticVariable(0x55, SimTime{5}, 0);
  SampledValue expr = SampleSingleVariableExpression(var);
  EXPECT_EQ(expr.value, var.value);
  EXPECT_EQ(expr.mode, var.mode);
}

TEST(ConcurrentAssertionSampling, ConstCastUsesCurrentValueOfArgument) {
  SampledValue sv = SampleConstCastExpression(0xBEEF);
  EXPECT_EQ(sv.value, 0xBEEFu);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, TriggeredAndMatchedUseCurrentReturnedValue) {
  SampledValue t = SampledValueOfTriggered(true);
  EXPECT_EQ(t.value, 1u);
  EXPECT_EQ(t.mode, SampleMode::kCurrent);
  SampledValue m = SampledValueOfMatched(false);
  EXPECT_EQ(m.value, 0u);
  EXPECT_EQ(m.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, RecursiveExpressionBitwiseAndsSampledValues) {
  SampledValue a = SampleStaticVariable(0xF0F0, SimTime{1}, 0);
  SampledValue b = SampleStaticVariable(0x0FF0, SimTime{1}, 0);
  SampledValue combined = SampleRecursiveExpression(
      a, b, [](uint64_t x, uint64_t y) { return x & y; });
  EXPECT_EQ(combined.value, 0x00F0u);
  EXPECT_EQ(combined.mode, SampleMode::kPreponed);
}

TEST(ConcurrentAssertionSampling,
     RecursivePropagatesCurrentWhenSubexpressionCurrent) {
  SampledValue a = SampleStaticVariable(0x10, SimTime{1}, 0);
  SampledValue s_triggered = SampledValueOfTriggered(true);
  SampledValue combined = SampleRecursiveExpression(
      a, s_triggered, [](uint64_t x, uint64_t y) { return x | y; });
  EXPECT_EQ(combined.mode, SampleMode::kCurrent);
  EXPECT_EQ(combined.value, 0x11u);
}

TEST(ConcurrentAssertionSampling, OtherVariableOrNetDefaultIsTypeDefault) {
  SampledValue sv = DefaultSampledValueOfVariableOrNet(0);
  EXPECT_EQ(sv.value, 0u);
  EXPECT_EQ(sv.mode, SampleMode::kDefault);
}

TEST(ConcurrentAssertionSampling, DefaultSampledValueOfExpressionIsRecursive) {
  SampledValue a = DefaultSampledValueOfVariableOrNet(0xAA);
  SampledValue b = DefaultSampledValueOfVariableOrNet(0x55);
  SampledValue combined = SampleRecursiveExpression(
      a, b, [](uint64_t x, uint64_t y) { return x | y; });
  EXPECT_EQ(combined.value, 0xFFu);

  EXPECT_NE(combined.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, ClockingBlockInputMustUseStep1Sampling) {
  EXPECT_TRUE(IsClockingBlockInputSamplingValid(ClockingInputSkew::kStep1));
  EXPECT_FALSE(IsClockingBlockInputSamplingValid(ClockingInputSkew::kOther));
}

// One concurrent assertion on `a`, clocked by the posedge of `clk`, over a run
// whose only clock tick is in the time step `tick_line` writes. `a` and `clk`
// both settle to 0 at time 0 and `tick_line` is the whole of what happens at
// time 5, so the order it writes the two in is the only thing that varies
// between two sources built from this.
std::string SourceWithTickStep(const std::string& tick_line) {
  return "module m;\n"
         "  logic clk;\n"
         "  logic a;\n"
         "  int hits = 0;\n"
         "  int misses = 0;\n"
         "  assert property (@(posedge clk) a) hits = hits + 1;\n"
         "  else misses = misses + 1;\n"
         "  initial begin\n"
         "    clk = 1'b0; a = 1'b0;\n"
         "    #5 " +
         tick_line +
         "\n"
         "  end\n"
         "endmodule\n";
}

// §16.5.1: "The sampled value of a variable in a time slot corresponding to
// time greater than 0 is the value of this variable in the Preponed region of
// this time slot." The Preponed value of a time slot is settled before the slot
// begins, so nothing a process writes during the slot can change it and the
// order of the writes within the slot cannot change the verdict either.
//
// Both runs below drive one clock tick at time 5 and raise `a` in that same
// time step, one before the assignment to `clk` and one after. §16.5.1 gives
// each the value `a` held in the Preponed region of time 5, which is the 0 it
// settled to at time 0, so neither assertion passes.
//
// Either run on its own is satisfied by an implementation that reads `a` live:
// the one writing `a` second reads 0 and agrees by accident, and the one
// writing it first reads 1 and disagrees. The pair is the claim. Without
// sampling the counts are 1 and 0.
TEST(ConcurrentAssertionSampling, VerdictDoesNotDependOnWriteOrderInTheTick) {
  SimFixture before;
  auto* first_hits = RunAndFindVar(SourceWithTickStep("a = 1'b1; clk = 1'b1;"),
                                   before, "hits");
  ASSERT_NE(first_hits, nullptr);
  auto* first_misses = before.ctx.FindVariable("misses");
  ASSERT_NE(first_misses, nullptr);
  SimFixture after;
  auto* second_hits =
      RunAndFindVar(SourceWithTickStep("clk = 1'b1; a = 1'b1;"), after, "hits");
  ASSERT_NE(second_hits, nullptr);
  auto* second_misses = after.ctx.FindVariable("misses");
  ASSERT_NE(second_misses, nullptr);
  EXPECT_EQ(first_hits->value.ToUint64(), second_hits->value.ToUint64());
  EXPECT_EQ(first_misses->value.ToUint64(), second_misses->value.ToUint64());
  // Each run drove one tick, and each read the 0 that `a` carried into the time
  // step rather than the 1 written within it.
  EXPECT_EQ(first_hits->value.ToUint64(), 0u);
  EXPECT_EQ(first_misses->value.ToUint64(), 1u);
}

// §16.5.1: "The sampled value of a variable in a time slot corresponding to
// time 0 is its default sampled value", and the default sampled value of a
// static variable is "the value assigned in its declaration, or, in the absence
// of such an assignment, ... the default (or uninitialized) value of the
// corresponding type". `a` is declared `logic` and its declaration assigns
// nothing, so its default sampled value is 1'bx however early the initial
// procedure raises it.
//
// The single clock tick here is at time 0, in the same time step that assigns
// `a` its 1. The assertion reads 1'bx, which §12.4 makes false, so the fail
// action runs and the pass action does not. An implementation reading the live
// value reads 1 and counts the pass instead.
TEST(ConcurrentAssertionSampling, TimeZeroTickReadsTheDefaultSampledValue) {
  SimFixture f;
  const std::string kSrc =
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  int hits = 0;\n"
      "  int misses = 0;\n"
      "  assert property (@(posedge clk) a) hits = hits + 1;\n"
      "  else misses = misses + 1;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    clk = 1'b0;\n"
      "    clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  auto* hits = RunAndFindVar(kSrc, f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 0u);
  auto* misses = f.ctx.FindVariable("misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(misses->value.ToUint64(), 1u);
}

}  // namespace
