#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

TEST(ProceduralConcurrentAssertion, EnqueuePendingInstanceCapturesCurrentArgs) {
  ProceduralAssertionQueue q;
  EXPECT_EQ(q.Size(), 0u);

  PendingProceduralAssertion p;
  p.instance_name = "a1";
  p.kind = AssertionKind::kAssert;

  p.sampled_args.push_back(SampleAutomaticVariable(7));
  q.Enqueue(p);

  EXPECT_EQ(q.Size(), 1u);
  EXPECT_EQ(q.MaturedCount(), 0u);
  EXPECT_EQ(q.Entries().front().sampled_args.front().value, 7u);
  EXPECT_EQ(q.Entries().front().sampled_args.front().mode,
            SampleMode::kCurrent);
}

TEST(ProceduralConcurrentAssertion, MatureAllConfirmsEveryPendingInstance) {
  ProceduralAssertionQueue q;
  for (int i = 0; i < 3; ++i) {
    PendingProceduralAssertion p;
    p.instance_name = "p" + std::to_string(i);
    q.Enqueue(p);
  }
  EXPECT_EQ(q.MaturedCount(), 0u);

  q.MatureAll();

  EXPECT_EQ(q.MaturedCount(), 3u);
  for (const auto& e : q.Entries()) {
    EXPECT_TRUE(e.matured);
  }
}

TEST(ProceduralConcurrentAssertion, FlushClearsQueueSoNothingMatures) {
  ProceduralAssertionQueue q;
  PendingProceduralAssertion p;
  p.instance_name = "a";
  q.Enqueue(p);
  EXPECT_EQ(q.Size(), 1u);

  q.Flush();

  EXPECT_EQ(q.Size(), 0u);
  EXPECT_EQ(q.MaturedCount(), 0u);
}

TEST(ProceduralConcurrentAssertion, MultiplePendingInstancesPerTimeStep) {
  ProceduralAssertionQueue q;
  for (int i = 0; i < 5; ++i) {
    PendingProceduralAssertion p;
    p.instance_name = "loop_a";
    q.Enqueue(p);
  }
  EXPECT_EQ(q.Size(), 5u);
}

TEST(ProceduralConcurrentAssertion, EngineProvidesQueuePerProcess) {
  SvaEngine eng;
  auto& q1 = eng.GetProceduralQueue("proc1");
  auto& q2 = eng.GetProceduralQueue("proc2");

  PendingProceduralAssertion p;
  p.instance_name = "x";
  q1.Enqueue(p);

  EXPECT_EQ(q1.Size(), 1u);
  EXPECT_EQ(q2.Size(), 0u);
}

TEST(ProceduralConcurrentAssertion,
     StaticConcurrentAssertionIsTheNonProceduralCase) {
  EXPECT_TRUE(IsStaticConcurrentAssertion(false));
  EXPECT_FALSE(IsStaticConcurrentAssertion(true));
}

TEST(ProceduralConcurrentAssertion,
     MaturedQueueHoldsInstanceUntilNextClockTick) {
  MaturedAssertionQueue mq;
  EXPECT_EQ(mq.Size(), 0u);

  PendingProceduralAssertion p;
  p.instance_name = "waiting_for_clock";
  mq.Place(p);
  EXPECT_EQ(mq.Size(), 1u);

  auto drained = mq.TakeAll();
  EXPECT_EQ(drained.size(), 1u);
  EXPECT_TRUE(drained.front().matured);
  EXPECT_EQ(drained.front().instance_name, "waiting_for_clock");
  EXPECT_EQ(mq.Size(), 0u);
}

TEST(ProceduralConcurrentAssertion, AutomaticVariableForbiddenInClockingEvent) {
  EXPECT_TRUE(IsAutomaticAllowedInClockingEvent(false));
  EXPECT_FALSE(IsAutomaticAllowedInClockingEvent(true));
}

TEST(ProceduralConcurrentAssertion, ClockInferredFromProceduralContextFirst) {
  InferredClock c =
      InferClockForProceduralConcurrentAssertion("clk_proc", "clk_default");
  EXPECT_EQ(c.kind, InferredClockKind::kFromProceduralContext);
  EXPECT_EQ(c.signal_name, "clk_proc");
}

TEST(ProceduralConcurrentAssertion, ClockInferredFromDefaultClockingFallback) {
  InferredClock c =
      InferClockForProceduralConcurrentAssertion("", "clk_default");
  EXPECT_EQ(c.kind, InferredClockKind::kFromDefaultClocking);
  EXPECT_EQ(c.signal_name, "clk_default");
}

TEST(ProceduralConcurrentAssertion, ClockInferenceFailsWhenNoContextAvailable) {
  InferredClock c = InferClockForProceduralConcurrentAssertion("", "");
  EXPECT_EQ(c.kind, InferredClockKind::kNotInferrable);
  EXPECT_EQ(c.signal_name, "");
}

TEST(ProceduralConcurrentAssertion, ClockInferenceRequiresAllThreeConditions) {
  EXPECT_TRUE(SatisfiesClockInferenceRequirements(true, true, true));

  EXPECT_FALSE(SatisfiesClockInferenceRequirements(false, true, true));
  EXPECT_FALSE(SatisfiesClockInferenceRequirements(true, false, true));
  EXPECT_FALSE(SatisfiesClockInferenceRequirements(true, true, false));

  EXPECT_FALSE(SatisfiesClockInferenceRequirements(false, false, false));
}

}  // namespace
