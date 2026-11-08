#include <gtest/gtest.h>

#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sampling.h"

using namespace delta;

namespace {

PendingProceduralAssertion MakePending(const char* name) {
  PendingProceduralAssertion p;
  p.instance_name = name;
  p.kind = AssertionKind::kAssert;
  return p;
}

TEST(DisablingProceduralAssertions, SpecificAssertionClearsOnlyItsPending) {
  ProceduralAssertionQueue q;
  q.Enqueue(MakePending("a1"));
  q.Enqueue(MakePending("a1"));
  q.Enqueue(MakePending("a2"));
  ASSERT_EQ(q.Size(), 3u);

  q.FlushPendingForInstance("a1");

  ASSERT_EQ(q.Size(), 1u);
  EXPECT_EQ(q.Entries().front().instance_name, "a2");
}

TEST(DisablingProceduralAssertions, EngineSpecificAssertionDisable) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("b1");
  q.Enqueue(MakePending("a1"));
  q.Enqueue(MakePending("other"));
  ASSERT_EQ(q.Size(), 2u);

  engine.ApplyDisableToProceduralAssertions(
      "b1", DisableTarget::kSpecificAssertion, "a1");

  auto& after = engine.GetProceduralQueue("b1");
  ASSERT_EQ(after.Size(), 1u);
  EXPECT_EQ(after.Entries().front().instance_name, "other");
}

TEST(DisablingProceduralAssertions, SpecificAssertionDisableIsPerProcess) {
  SvaEngine engine;
  engine.GetProceduralQueue("p1").Enqueue(MakePending("a1"));
  engine.GetProceduralQueue("p2").Enqueue(MakePending("a1"));

  engine.ApplyDisableToProceduralAssertions(
      "p1", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(engine.GetProceduralQueue("p1").Size(), 0u);
  EXPECT_EQ(engine.GetProceduralQueue("p2").Size(), 1u);
}

TEST(DisablingProceduralAssertions, OutermostScopeFlushesWholeQueue) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("b2");
  q.Enqueue(MakePending("a2"));
  q.Enqueue(MakePending("a3"));
  ASSERT_EQ(q.Size(), 2u);

  engine.ApplyDisableToProceduralAssertions("b2",
                                            DisableTarget::kOutermostScope, {});

  EXPECT_EQ(engine.GetProceduralQueue("b2").Size(), 0u);
}

TEST(DisablingProceduralAssertions, MaturedSurvivesSpecificAssertionDisable) {
  ProceduralAssertionQueue q;
  q.Enqueue(MakePending("a1"));
  q.MatureAll();
  q.Enqueue(MakePending("a1"));
  ASSERT_EQ(q.Size(), 2u);
  ASSERT_EQ(q.MaturedCount(), 1u);

  q.FlushPendingForInstance("a1");

  EXPECT_EQ(q.Size(), 1u);
  EXPECT_EQ(q.MaturedCount(), 1u);
}

TEST(DisablingProceduralAssertions, MaturedSurvivesOutermostScopeDisable) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("b2");
  q.Enqueue(MakePending("a2"));
  q.MatureAll();
  q.Enqueue(MakePending("a3"));
  ASSERT_EQ(q.Size(), 2u);

  engine.ApplyDisableToProceduralAssertions("b2",
                                            DisableTarget::kOutermostScope, {});

  EXPECT_EQ(engine.GetProceduralQueue("b2").Size(), 1u);
  EXPECT_EQ(engine.GetProceduralQueue("b2").MaturedCount(), 1u);
}

TEST(DisablingProceduralAssertions, TaskDisableLeavesQueueIntact) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("p");
  q.Enqueue(MakePending("a"));
  q.Enqueue(MakePending("a"));

  engine.ApplyDisableToProceduralAssertions("p", DisableTarget::kTask, {});

  EXPECT_EQ(engine.GetProceduralQueue("p").Size(), 2u);
}

TEST(DisablingProceduralAssertions, NonOutermostScopeDisableLeavesQueueIntact) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("p");
  q.Enqueue(MakePending("a"));

  engine.ApplyDisableToProceduralAssertions(
      "p", DisableTarget::kNonOutermostScope, {});

  EXPECT_EQ(engine.GetProceduralQueue("p").Size(), 1u);
}

TEST(DisablingProceduralAssertions,
     SpecificAssertionDisableForAbsentNameKeepsQueue) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("b1");
  q.Enqueue(MakePending("other"));
  q.Enqueue(MakePending("other"));
  ASSERT_EQ(q.Size(), 2u);

  engine.ApplyDisableToProceduralAssertions(
      "b1", DisableTarget::kSpecificAssertion, "not_queued");

  EXPECT_EQ(engine.GetProceduralQueue("b1").Size(), 2u);
}

TEST(DisablingProceduralAssertions,
     SpecificAssertionDisableOnEmptyQueueIsNoOp) {
  SvaEngine engine;
  engine.ApplyDisableToProceduralAssertions(
      "never_queued", DisableTarget::kSpecificAssertion, "a1");
  EXPECT_EQ(engine.GetProceduralQueue("never_queued").Size(), 0u);
}

TEST(DisablingProceduralAssertions, OutermostScopeDisableOnEmptyQueueIsNoOp) {
  SvaEngine engine;
  engine.ApplyDisableToProceduralAssertions("never_queued",
                                            DisableTarget::kOutermostScope, {});
  EXPECT_EQ(engine.GetProceduralQueue("never_queued").Size(), 0u);
}

TEST(DisablingProceduralAssertions, AllMaturedSurviveSpecificAssertionDisable) {
  ProceduralAssertionQueue q;
  q.Enqueue(MakePending("a1"));
  q.Enqueue(MakePending("a1"));
  q.MatureAll();
  ASSERT_EQ(q.MaturedCount(), 2u);

  q.FlushPendingForInstance("a1");

  EXPECT_EQ(q.Size(), 2u);
  EXPECT_EQ(q.MaturedCount(), 2u);
}

}  // namespace
