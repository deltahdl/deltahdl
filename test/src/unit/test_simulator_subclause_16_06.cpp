#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

TEST(AssertionBooleanInterpretation, AllZeroKnownValueIsFalse) {
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0, 0));
}

TEST(AssertionBooleanInterpretation, AnyKnownNonZeroValueIsTrue) {
  EXPECT_TRUE(InterpretAssertionExprAsBoolean(1, 0));
  EXPECT_TRUE(InterpretAssertionExprAsBoolean(0xDEADBEEF, 0));
}

TEST(AssertionBooleanInterpretation, AnyUnknownBitForcesFalse) {
  // bval != 0 means at least one bit is x or z; the §16.6 rule treats that
  // the same as 0 — the expression is interpreted as false.
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0xFFFFFFFF, 0x1));
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0x1, 0x1));
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0x0, 0xFF));
}

TEST(AssertionBooleanInterpretation, MaximumKnownValueIsTrue) {
  // Boundary case: every bit known and set — Boolean interpretation is true.
  EXPECT_TRUE(
      InterpretAssertionExprAsBoolean(std::numeric_limits<uint64_t>::max(), 0));
}

TEST(AssertionBooleanInterpretation, AllBitsUnknownIsFalse) {
  // Boundary case: every bit unknown (bval saturated). Even with aval also
  // saturated, the §16.6 coercion treats this as false.
  EXPECT_FALSE(
      InterpretAssertionExprAsBoolean(std::numeric_limits<uint64_t>::max(),
                                      std::numeric_limits<uint64_t>::max()));
  EXPECT_FALSE(
      InterpretAssertionExprAsBoolean(0, std::numeric_limits<uint64_t>::max()));
}

TEST(AssertionSampledArrayElement, SurvivesArrayMutationDuringEvaluationScope) {
  SampledArrayElement s = SampleArrayElementForAssertion(0xABCD);
  EXPECT_TRUE(SampledArrayElementStillReadable(s));

  // The container resizes / removes the underlying element. Per §16.6 the
  // sampled copy must remain readable until the evaluation completes.
  SampledArrayElement after = ArrayElementAfterArrayMutation(s);
  EXPECT_TRUE(SampledArrayElementStillReadable(after));
  EXPECT_EQ(after.value, 0xABCDu);
}

TEST(AssertionSampledArrayElement,
     SurvivesRepeatedMutationsUntilEvaluationCompletes) {
  // §16.6 lists both "removed from the array" and "the array may get resized"
  // as ways the underlying storage can change. The sampled copy must remain
  // intact across any number of such mutations during evaluation scope.
  SampledArrayElement s = SampleArrayElementForAssertion(0x1234);
  for (int i = 0; i < 16; ++i) {
    s = ArrayElementAfterArrayMutation(s);
    EXPECT_TRUE(SampledArrayElementStillReadable(s));
    EXPECT_EQ(s.value, 0x1234u);
  }
}

TEST(AssertionBooleanExprPlace, SequenceOrPropertyExpressionsUseSampledValues) {
  EXPECT_TRUE(
      BooleanExprUsesSampledValues(BooleanExprPlace::kSequenceOrPropertyExpr));
}

TEST(AssertionBooleanExprPlace, ClockingEventIsExceptedFromSampledRule) {
  // §16.6 explicitly excepts clocking-event expressions, which follow §16.5
  // instead. The two-rail input is irrelevant here; only the place matters.
  EXPECT_FALSE(BooleanExprUsesSampledValues(BooleanExprPlace::kClockingEvent));
}

TEST(AssertionBooleanExprPlace, DisableConditionUsesCurrentValuesNotSampled) {
  EXPECT_FALSE(
      BooleanExprUsesSampledValues(BooleanExprPlace::kDisableCondition));
  EXPECT_TRUE(DisableConditionUsesCurrentValues());
}

}  // namespace
