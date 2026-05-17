#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.5.1: "The sampled value of a variable in a time slot corresponding
// to time greater than 0 is the value of this variable in the Preponed
// region of this time slot."  Observe that SampleStaticVariable returns
// the Preponed value with kPreponed mode when t > 0.
TEST(ConcurrentAssertionSampling, StaticVariableSamplesPreponedAtNonzeroTime) {
  SampledValue sv =
      SampleStaticVariable(/*preponed=*/0x1234, SimTime{10}, /*default=*/0);
  EXPECT_EQ(sv.value, 0x1234u);
  EXPECT_EQ(sv.mode, SampleMode::kPreponed);
}

// §16.5.1: "The sampled value of a variable in a time slot corresponding
// to time 0 is its default sampled value."  Observe that
// SampleStaticVariable returns the type default with kDefault mode at
// time 0 regardless of the Preponed argument.
TEST(ConcurrentAssertionSampling, StaticVariableSamplesDefaultAtTimeZero) {
  SampledValue sv = SampleStaticVariable(/*preponed=*/0xDEAD, SimTime{0},
                                         /*type_default=*/0);
  EXPECT_EQ(sv.value, 0u);
  EXPECT_EQ(sv.mode, SampleMode::kDefault);
}

// §16.5.1: "Sampled values of automatic variables (see 16.14.6), local
// variables (see 16.10), and active free checker variables are their
// current values."  Observe that SampleAutomaticVariable returns the
// current value with kCurrent mode — this is the rule §16.14.6 relies on
// when capturing arguments for the procedural assertion queue.
TEST(ConcurrentAssertionSampling, AutomaticVariableSamplesCurrentValue) {
  SampledValue sv = SampleAutomaticVariable(/*current=*/0xABCD);
  EXPECT_EQ(sv.value, 0xABCDu);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

// §16.5.1: "The default sampled value of the `triggered` event method
// (see 15.5.3) and the sequence methods `triggered` and `matched` is
// false (1'b0)."  Observe both helpers return 0.
TEST(ConcurrentAssertionSampling, DefaultSampledValueOfTriggeredIsZero) {
  SampledValue t = DefaultSampledValueOfTriggered();
  EXPECT_EQ(t.value, 0u);
  SampledValue m = DefaultSampledValueOfMatched();
  EXPECT_EQ(m.value, 0u);
}

// §16.5.1: "The sampled value of an expression consisting of a single
// variable is the sampled value of this variable."  Observe that the
// wrapper forwards the variable's SampledValue unchanged so an
// expression that is itself a single variable is sampled identically.
TEST(ConcurrentAssertionSampling, SingleVariableExpressionForwardsVariableSample) {
  SampledValue var = SampleStaticVariable(0x55, SimTime{5}, /*default=*/0);
  SampledValue expr = SampleSingleVariableExpression(var);
  EXPECT_EQ(expr.value, var.value);
  EXPECT_EQ(expr.mode, var.mode);
}

// §16.5.1: "The sampled value of a `const` cast expression ... is
// defined as the current value of its argument.  For example ... the
// sampled value of const'(a) is the current value of a."  Observe that
// the result carries the current value and kCurrent mode regardless of
// what the Preponed value would have been.
TEST(ConcurrentAssertionSampling, ConstCastUsesCurrentValueOfArgument) {
  SampledValue sv = SampleConstCastExpression(/*current=*/0xBEEF);
  EXPECT_EQ(sv.value, 0xBEEFu);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

// §16.5.1: "The sampled value of the `triggered` event method and the
// sequence methods `triggered` and `matched` ... is defined as the
// current value returned by the event property or sequence method."
// Observe that the helpers carry the current-returned value with
// kCurrent mode.
TEST(ConcurrentAssertionSampling, TriggeredAndMatchedUseCurrentReturnedValue) {
  SampledValue t = SampledValueOfTriggered(/*current_returned=*/true);
  EXPECT_EQ(t.value, 1u);
  EXPECT_EQ(t.mode, SampleMode::kCurrent);
  SampledValue m = SampledValueOfMatched(/*current_returned=*/false);
  EXPECT_EQ(m.value, 0u);
  EXPECT_EQ(m.mode, SampleMode::kCurrent);
}

// §16.5.1: "The sampled value of any other expression is defined
// recursively using the values of its arguments.  For example, the
// sampled value of an expression e1 & e2 ... is the bitwise AND of the
// sampled values of e1 and e2."  Observe that the recursive sampler
// combines two already-sampled subexpressions and propagates kCurrent
// when any subexpression is kCurrent.
TEST(ConcurrentAssertionSampling, RecursiveExpressionBitwiseAndsSampledValues) {
  SampledValue a = SampleStaticVariable(0xF0F0, SimTime{1}, /*default=*/0);
  SampledValue b = SampleStaticVariable(0x0FF0, SimTime{1}, /*default=*/0);
  SampledValue combined =
      SampleRecursiveExpression(a, b, [](uint64_t x, uint64_t y) {
        return x & y;
      });
  EXPECT_EQ(combined.value, 0x00F0u);
  EXPECT_EQ(combined.mode, SampleMode::kPreponed);
}

// §16.5.1: "In particular, if an expression contains a function call, to
// evaluate the sampled value of this expression, the function is called
// on the sampled values of its arguments at the time of the expression
// evaluation. For example, if ... s is a sequence, and f is a function,
// the sampled value of f(a, s.triggered) is the result of the
// application of f to the sampled values of a and s.triggered, i.e., to
// the value of a taken from the Preponed region and to the current
// value of s.triggered."  Observe that when one subexpression is
// kCurrent (triggered) and another is kPreponed (static variable), the
// recursive sampler propagates kCurrent.
TEST(ConcurrentAssertionSampling, RecursivePropagatesCurrentWhenSubexpressionCurrent) {
  SampledValue a = SampleStaticVariable(0x10, SimTime{1}, /*default=*/0);
  SampledValue s_triggered = SampledValueOfTriggered(true);
  SampledValue combined =
      SampleRecursiveExpression(a, s_triggered, [](uint64_t x, uint64_t y) {
        return x | y;
      });
  EXPECT_EQ(combined.mode, SampleMode::kCurrent);
  EXPECT_EQ(combined.value, 0x11u);
}

// §16.5.1: "The default sampled value of any other variable or net is
// the default value of the corresponding type.  For example, the
// default sampled value of variable y of type logic is 1'bx."  Observe
// that the helper carries the type default with kDefault mode — no
// declared-initializer fallback unlike the static-variable case.
TEST(ConcurrentAssertionSampling, OtherVariableOrNetDefaultIsTypeDefault) {
  SampledValue sv = DefaultSampledValueOfVariableOrNet(/*type_default=*/0);
  EXPECT_EQ(sv.value, 0u);
  EXPECT_EQ(sv.mode, SampleMode::kDefault);
}

// §16.5.1: "The default sampled value of an expression is defined
// recursively by evaluating the expression using the default sampled
// values of its component subexpressions and variables."  Observe that
// combining two default-mode subexpressions yields a result whose mode
// is not kCurrent — the recursion preserves the default-region
// classification.
TEST(ConcurrentAssertionSampling, DefaultSampledValueOfExpressionIsRecursive) {
  SampledValue a = DefaultSampledValueOfVariableOrNet(0xAA);
  SampledValue b = DefaultSampledValueOfVariableOrNet(0x55);
  SampledValue combined =
      SampleRecursiveExpression(a, b, [](uint64_t x, uint64_t y) {
        return x | y;
      });
  EXPECT_EQ(combined.value, 0xFFu);
  // §16.5.1: when no subexpression is kCurrent, the recursion stays in
  // Preponed/Default territory — kCurrent does not appear.
  EXPECT_NE(combined.mode, SampleMode::kCurrent);
}

// §16.5.1: "If a variable is an input variable of a clocking block,
// the variable shall be sampled by the clocking block with #1step
// sampling.  Any other type of sampling for the clocking block
// variable shall result in an error."  Observe that #1step is accepted
// and any other skew is rejected.
TEST(ConcurrentAssertionSampling, ClockingBlockInputMustUseStep1Sampling) {
  EXPECT_TRUE(IsClockingBlockInputSamplingValid(ClockingInputSkew::kStep1));
  EXPECT_FALSE(IsClockingBlockInputSamplingValid(ClockingInputSkew::kOther));
}

}  // namespace
