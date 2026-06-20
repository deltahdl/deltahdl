#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

TEST(ProceduralAssertionArgs, ConstAndAutomaticArgsAreSnapshotAtQueueTime) {
  SampledValue from_const = SampleProceduralAssertionArgument(7);
  EXPECT_EQ(from_const.value, 7u);
  EXPECT_EQ(from_const.mode, SampleMode::kCurrent);

  SampledValue from_auto = SampleProceduralAssertionArgument(3);
  EXPECT_EQ(from_auto.value, 3u);
  EXPECT_EQ(from_auto.mode, SampleMode::kCurrent);
}

TEST(ProceduralAssertionArgs, StaticVariableInExpressionUsesPreponed) {
  SampledValue s = SampleStaticVariable(10, SimTime{1}, 0);
  EXPECT_EQ(s.value, 10u);
  EXPECT_EQ(s.mode, SampleMode::kPreponed);
}

TEST(ProceduralAssertionArgs,
     ProceduralExecutionAffectsActivationNotCompletion) {
  EXPECT_TRUE(
      ProceduralExecutionAffects(ProceduralExecutionEffect::kActivation, true));

  EXPECT_FALSE(
      ProceduralExecutionAffects(ProceduralExecutionEffect::kCompletion, true));

  EXPECT_TRUE(ProceduralExecutionAffects(ProceduralExecutionEffect::kActivation,
                                         false));
  EXPECT_TRUE(ProceduralExecutionAffects(ProceduralExecutionEffect::kCompletion,
                                         false));
}

TEST(ProceduralAssertionArgs,
     ActionBlockArgumentSamplingMatchesAssertionArgument) {
  SampledValue arg = SampleProceduralAssertionArgument(5);
  SampledValue ab = SampleProceduralAssertionActionBlockArgument(5);

  EXPECT_EQ(ab.value, arg.value);
  EXPECT_EQ(ab.mode, arg.mode);
}

TEST(ProceduralAssertionArgs, ActionBlockCannotModifyCapturedArgument) {
  EXPECT_FALSE(ActionBlockMayModifyArgument());
}

TEST(ProceduralAssertionArgs, EnclosingConditionalUsesCurrentValueNotSampled) {
  uint64_t guard = ReadProceduralConditionalGuard(1, 0);
  EXPECT_EQ(guard, 1u);

  uint64_t guard2 = ReadProceduralConditionalGuard(0, 1);
  EXPECT_EQ(guard2, 0u);
}

TEST(ProceduralAssertionArgs, AssertionExpressionStillUsesSampledValues) {
  EXPECT_TRUE(ConcurrentTimingUsesSampledValues(AssertionTiming::kConcurrent));
}

TEST(ProceduralAssertionArgs,
     EnqueuedSnapshotIsWhatEvaluationReadsAfterMature) {
  PendingProceduralAssertion p;
  p.instance_name = "a_args";
  p.kind = AssertionKind::kAssert;
  p.sampled_args.push_back(SampleProceduralAssertionArgument(6));

  ProceduralAssertionQueue q;
  q.Enqueue(p);
  q.MatureAll();

  ASSERT_EQ(q.Entries().size(), 1u);
  const auto& stored = q.Entries().front().sampled_args.front();
  EXPECT_EQ(stored.value, 6u);
  EXPECT_EQ(stored.mode, SampleMode::kCurrent);

  SampledValue post = ProceduralArgumentValueAfterMature(stored, 999);
  EXPECT_EQ(post.value, 6u);
  EXPECT_EQ(post.mode, SampleMode::kCurrent);
}

TEST(ProceduralAssertionArgs, StaticVariableAtTimeZeroFallsBackToTypeDefault) {
  SampledValue s = SampleStaticVariable(42, SimTime{0}, 0);
  EXPECT_EQ(s.value, 0u);
  EXPECT_EQ(s.mode, SampleMode::kDefault);
}

TEST(ProceduralAssertionArgs, ImmediateTimingDoesNotUseSampledValues) {
  EXPECT_FALSE(ConcurrentTimingUsesSampledValues(AssertionTiming::kImmediate));
}

TEST(ProceduralAssertionArgs, MultipleQueuedInstancesEachHoldTheirOwnSnapshot) {
  ProceduralAssertionQueue q;
  for (uint64_t i = 0; i < 10; ++i) {
    PendingProceduralAssertion p;
    p.instance_name = "loop_a3";
    p.sampled_args.push_back(SampleProceduralAssertionArgument(i));
    q.Enqueue(p);
  }
  q.MatureAll();

  ASSERT_EQ(q.Entries().size(), 10u);
  for (uint64_t i = 0; i < 10; ++i) {
    const auto& stored =
        q.Entries()[static_cast<size_t>(i)].sampled_args.front();
    EXPECT_EQ(stored.value, i);
    EXPECT_EQ(stored.mode, SampleMode::kCurrent);

    SampledValue post = ProceduralArgumentValueAfterMature(stored, 0xDEAD);
    EXPECT_EQ(post.value, i);
  }
}

TEST(ProceduralAssertionArgs, ActionBlockArgumentRemainsConstantAfterMature) {
  SampledValue captured = SampleProceduralAssertionActionBlockArgument(11);

  SampledValue post = ProceduralArgumentValueAfterMature(captured, 0);
  EXPECT_EQ(post.value, 11u);
  EXPECT_EQ(post.mode, SampleMode::kCurrent);
}

TEST(ProceduralAssertionArgs, SnapshotCapturesBoundaryValuesExactly) {
  SampledValue lo = SampleProceduralAssertionArgument(0);
  EXPECT_EQ(lo.value, 0u);
  EXPECT_EQ(lo.mode, SampleMode::kCurrent);

  uint64_t max = std::numeric_limits<uint64_t>::max();
  SampledValue hi = SampleProceduralAssertionArgument(max);
  EXPECT_EQ(hi.value, max);
  EXPECT_EQ(hi.mode, SampleMode::kCurrent);
}

TEST(ProceduralAssertionArgs, GuardIgnoresSampledWhenCurrentDiffers) {
  uint64_t big_sampled = std::numeric_limits<uint64_t>::max();
  EXPECT_EQ(ReadProceduralConditionalGuard(0, big_sampled), 0u);
  EXPECT_EQ(ReadProceduralConditionalGuard(7, big_sampled), 7u);
}

}  // namespace
