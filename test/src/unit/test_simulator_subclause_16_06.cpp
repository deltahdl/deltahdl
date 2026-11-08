#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

#include "fixture_simulator.h"
#include "simulator/sva_engine_sampling.h"

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
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0xFFFFFFFF, 0x1));
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0x1, 0x1));
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0x0, 0xFF));
}

TEST(AssertionBooleanInterpretation, MaximumKnownValueIsTrue) {
  EXPECT_TRUE(
      InterpretAssertionExprAsBoolean(std::numeric_limits<uint64_t>::max(), 0));
}

TEST(AssertionBooleanInterpretation, AllBitsUnknownIsFalse) {
  EXPECT_FALSE(
      InterpretAssertionExprAsBoolean(std::numeric_limits<uint64_t>::max(),
                                      std::numeric_limits<uint64_t>::max()));
  EXPECT_FALSE(
      InterpretAssertionExprAsBoolean(0, std::numeric_limits<uint64_t>::max()));
}

TEST(AssertionSampledArrayElement, SurvivesArrayMutationDuringEvaluationScope) {
  SampledArrayElement s = SampleArrayElementForAssertion(0xABCD);
  EXPECT_TRUE(SampledArrayElementStillReadable(s));

  SampledArrayElement after = ArrayElementAfterArrayMutation(s);
  EXPECT_TRUE(SampledArrayElementStillReadable(after));
  EXPECT_EQ(after.value, 0xABCDu);
}

TEST(AssertionSampledArrayElement,
     SurvivesRepeatedMutationsUntilEvaluationCompletes) {
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
  EXPECT_FALSE(BooleanExprUsesSampledValues(BooleanExprPlace::kClockingEvent));
}

TEST(AssertionBooleanExprPlace, DisableConditionUsesCurrentValuesNotSampled) {
  EXPECT_FALSE(
      BooleanExprUsesSampledValues(BooleanExprPlace::kDisableCondition));
  EXPECT_TRUE(DisableConditionUsesCurrentValues());
}

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
