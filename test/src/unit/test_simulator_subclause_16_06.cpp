#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

#include "fixture_simulator.h"
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

// §16.6: an element of a queue sampled for an assertion's evaluation continues
// to exist for that evaluation though the queue sheds it before the evaluation
// runs. q holds 5 from time zero; in the time step of the one tick the initial
// block empties q before raising the clock, and the property still reads the
// 5 sampled in the Preponed region, so the pass statement counts once. Read
// live, q[0] is the absent element's 0 and the count stays at zero.
TEST(AssertionSampledArrayElement, QueueHeadSampledForTheTickOutlivesThePop) {
  SimFixture f;
  auto* held = RunAndFindVar(
      "module m;\n"
      "  logic clk = 0;\n"
      "  int q[$];\n"
      "  int held = 0;\n"
      "  assert property (@(posedge clk) q[0] == 5) held = held + 1;\n"
      "  initial begin\n"
      "    q.push_back(5);\n"
      "    #5 q.pop_front(); clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "held");
  ASSERT_NE(held, nullptr);
  EXPECT_EQ(held->value.ToUint64(), 1u);
}

}  // namespace
