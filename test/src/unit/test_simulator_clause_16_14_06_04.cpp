#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

PendingProceduralAssertion MakePending(const char* name) {
  PendingProceduralAssertion p;
  p.instance_name = name;
  p.kind = AssertionKind::kAssert;
  return p;
}

// §16.14.6.4 (bullet 1): disabling one specific procedural concurrent assertion
// clears that assertion's pending instances while leaving other assertions'
// pending instances in the queue.
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

// §16.14.6.4 (bullet 1): the per-assertion disable is exercised through the
// engine entry point; only the named assertion's pending instances of the
// addressed process are cleared.
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

// §16.14.6.4 (bullet 1): the per-assertion disable addresses one process, so
// another process's pending instances of the same-named assertion are left in
// place.
TEST(DisablingProceduralAssertions, SpecificAssertionDisableIsPerProcess) {
  SvaEngine engine;
  engine.GetProceduralQueue("p1").Enqueue(MakePending("a1"));
  engine.GetProceduralQueue("p2").Enqueue(MakePending("a1"));

  engine.ApplyDisableToProceduralAssertions(
      "p1", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(engine.GetProceduralQueue("p1").Size(), 0u);
  EXPECT_EQ(engine.GetProceduralQueue("p2").Size(), 1u);
}

// §16.14.6.4 (bullet 2): disabling the outermost scope of a procedure flushes
// the whole pending procedural assertion queue of that process.
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

// §16.14.6.4: once an evaluation attempt has matured it is not impacted by a
// disable of its specific assertion; only the still-pending instance is
// cleared.
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

// §16.14.6.4: once an evaluation attempt has matured it is not impacted by a
// disable of the outermost scope either; the matured attempt stays queued.
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

// §16.14.6.4: disabling a task does not flush any pending procedural assertion
// instances of the process.
TEST(DisablingProceduralAssertions, TaskDisableLeavesQueueIntact) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("p");
  q.Enqueue(MakePending("a"));
  q.Enqueue(MakePending("a"));

  engine.ApplyDisableToProceduralAssertions("p", DisableTarget::kTask, {});

  EXPECT_EQ(engine.GetProceduralQueue("p").Size(), 2u);
}

// §16.14.6.4: disabling a non-outermost scope of a procedure does not flush any
// pending procedural assertion instances.
TEST(DisablingProceduralAssertions, NonOutermostScopeDisableLeavesQueueIntact) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("p");
  q.Enqueue(MakePending("a"));

  engine.ApplyDisableToProceduralAssertions(
      "p", DisableTarget::kNonOutermostScope, {});

  EXPECT_EQ(engine.GetProceduralQueue("p").Size(), 1u);
}

// §16.14.6.4 (bullet 1), edge case: disabling an assertion that has no pending
// instances in the queue clears nothing; every other assertion's pending
// instances are left in place.
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

// §16.14.6.4 (bullet 1), edge case: a specific-assertion disable on a process
// with no queued instances is a safe no-op.
TEST(DisablingProceduralAssertions,
     SpecificAssertionDisableOnEmptyQueueIsNoOp) {
  SvaEngine engine;
  engine.ApplyDisableToProceduralAssertions(
      "never_queued", DisableTarget::kSpecificAssertion, "a1");
  EXPECT_EQ(engine.GetProceduralQueue("never_queued").Size(), 0u);
}

// §16.14.6.4 (bullet 2), edge case: an outermost-scope disable on a process
// with no queued instances is a safe no-op.
TEST(DisablingProceduralAssertions, OutermostScopeDisableOnEmptyQueueIsNoOp) {
  SvaEngine engine;
  engine.ApplyDisableToProceduralAssertions("never_queued",
                                            DisableTarget::kOutermostScope, {});
  EXPECT_EQ(engine.GetProceduralQueue("never_queued").Size(), 0u);
}

// §16.14.6.4, edge case for the matured-immunity rule: when every queued
// instance of the named assertion has already matured, a specific-assertion
// disable removes none of them.
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
