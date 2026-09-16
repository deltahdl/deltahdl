#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

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

// §16.14.6.1 (examples a2/a3): a `const'(i)` cast argument — the const-cast
// construct supplied by dependency §16.5.1 — is captured at its current value
// when the evaluation attempt is queued, and that captured value is what the
// evaluation reads after the instance matures, regardless of later changes to
// the underlying variable. This exercises the const-expression input form of
// the argument-capture rule directly, rather than through the generic sampler.
TEST(ProceduralAssertionArgs,
     ConstCastArgumentIsSnapshotAsCurrentAndSurvivesMature) {
  PendingProceduralAssertion p;
  p.instance_name = "a3";
  p.kind = AssertionKind::kAssert;
  // foo[const'(i)] with i currently 4.
  p.sampled_args.push_back(SampleConstCastExpression(4));
  ASSERT_EQ(p.sampled_args.front().mode, SampleMode::kCurrent);

  ProceduralAssertionQueue q;
  q.Enqueue(p);
  q.MatureAll();

  ASSERT_EQ(q.Entries().size(), 1u);
  const auto& stored = q.Entries().front().sampled_args.front();
  EXPECT_EQ(stored.value, 4u);
  EXPECT_EQ(stored.mode, SampleMode::kCurrent);

  // i races ahead to its loop-final value; the queued const value is
  // unaffected.
  SampledValue post = ProceduralArgumentValueAfterMature(stored, 10);
  EXPECT_EQ(post.value, 4u);
  EXPECT_EQ(post.mode, SampleMode::kCurrent);
}

// §16.14.6.1 (example a4): a bare automatic-variable argument has its immediate
// value preserved at queue time exactly as a const-cast argument does, so the
// automatic input form of the capture rule yields the same current-value
// snapshot that survives maturation.
TEST(ProceduralAssertionArgs,
     AutomaticVariableArgumentIsSnapshotAsCurrentAndSurvivesMature) {
  PendingProceduralAssertion p;
  p.instance_name = "a4";
  p.kind = AssertionKind::kAssert;
  // foo[i] where i is declared in the for statement, so it is automatic.
  p.sampled_args.push_back(SampleAutomaticVariable(6));
  ASSERT_EQ(p.sampled_args.front().mode, SampleMode::kCurrent);

  ProceduralAssertionQueue q;
  q.Enqueue(p);
  q.MatureAll();

  const auto& stored = q.Entries().front().sampled_args.front();
  EXPECT_EQ(stored.value, 6u);
  EXPECT_EQ(stored.mode, SampleMode::kCurrent);

  SampledValue post = ProceduralArgumentValueAfterMature(stored, 10);
  EXPECT_EQ(post.value, 6u);
  EXPECT_EQ(post.mode, SampleMode::kCurrent);
}

// §16.14.6.1 (example a2): within a single queued instance the two argument
// forms keep their distinct capture modes. In `foo[const'(i)] && bar[i]` with i
// a static loop variable, the const-cast argument is captured at its current
// value (0..9) while the bare static argument is sampled in the Preponed region
// (its settled loop-final value 10). Both live in the same instance's argument
// list and must not be conflated.
TEST(ProceduralAssertionArgs,
     MixedConstCastAndStaticArgsRetainDistinctCaptureModes) {
  PendingProceduralAssertion p;
  p.instance_name = "a2";
  p.kind = AssertionKind::kAssert;
  p.sampled_args.push_back(SampleConstCastExpression(3));  // foo[const'(i)]
  p.sampled_args.push_back(SampleStaticVariable(
      /*preponed_value=*/10, SimTime{1}, /*type_default=*/0));  // bar[i]

  ProceduralAssertionQueue q;
  q.Enqueue(p);
  q.MatureAll();

  ASSERT_EQ(q.Entries().size(), 1u);
  const auto& args = q.Entries().front().sampled_args;
  ASSERT_EQ(args.size(), 2u);

  EXPECT_EQ(args[0].value, 3u);
  EXPECT_EQ(args[0].mode, SampleMode::kCurrent);

  EXPECT_EQ(args[1].value, 10u);
  EXPECT_EQ(args[1].mode, SampleMode::kPreponed);
}

}  // namespace
