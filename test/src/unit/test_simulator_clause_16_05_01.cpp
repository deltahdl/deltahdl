#include <gtest/gtest.h>

#include "common/types.h"
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

}  // namespace
