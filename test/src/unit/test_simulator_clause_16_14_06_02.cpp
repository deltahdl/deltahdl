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

// §16.14.6.2: a process that resumes after suspending at an event control is
// at a flush point.
TEST(ProceduralAssertionFlushPoints, EventControlResumeIsFlushPoint) {
  EXPECT_TRUE(
      IsProceduralAssertionFlushPoint(FlushPointReason::kEventControlResume));
}

// §16.14.6.2: a process that resumes after suspending at a wait statement is
// at a flush point.
TEST(ProceduralAssertionFlushPoints, WaitResumeIsFlushPoint) {
  EXPECT_TRUE(IsProceduralAssertionFlushPoint(FlushPointReason::kWaitResume));
}

// §16.14.6.2: an always_comb re-running on a dependent-signal transition is a
// flush point.
TEST(ProceduralAssertionFlushPoints, AlwaysCombSignalDeltaIsFlushPoint) {
  EXPECT_TRUE(IsProceduralAssertionFlushPoint(
      FlushPointReason::kAlwaysCombSignalDelta));
}

// §16.14.6.2: an always_latch re-running on a dependent-signal transition is a
// flush point.
TEST(ProceduralAssertionFlushPoints, AlwaysLatchSignalDeltaIsFlushPoint) {
  EXPECT_TRUE(IsProceduralAssertionFlushPoint(
      FlushPointReason::kAlwaysLatchSignalDelta));
}

// §16.14.6.2: disabling the outermost scope of the process is a flush point.
TEST(ProceduralAssertionFlushPoints, DisableOuterScopeIsFlushPoint) {
  EXPECT_TRUE(
      IsProceduralAssertionFlushPoint(FlushPointReason::kDisableOuterScope));
}

// §16.14.6.2: ordinary continuation that is not one of the listed events is not
// a flush point.
TEST(ProceduralAssertionFlushPoints, NoneIsNotAFlushPoint) {
  EXPECT_FALSE(IsProceduralAssertionFlushPoint(FlushPointReason::kNone));
}

// §16.14.6.2: reaching a flush point discards the pending instances queued for
// that process before they can mature (the a1/b1 example).
TEST(ProceduralAssertionFlushPoints, EventResumeFlushesPendingInstances) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("b1");
  q.Enqueue(MakePending("a1"));
  q.Enqueue(MakePending("a1"));
  ASSERT_EQ(q.Size(), 2u);

  engine.OnProceduralAssertionFlushPoint("b1",
                                         FlushPointReason::kEventControlResume);
  EXPECT_EQ(engine.GetProceduralQueue("b1").Size(), 0u);
}

// §16.14.6.2: a non-flush-point continuation leaves the pending queue intact.
TEST(ProceduralAssertionFlushPoints, NoneReasonDoesNotFlush) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("p");
  q.Enqueue(MakePending("a"));
  q.Enqueue(MakePending("a"));

  engine.OnProceduralAssertionFlushPoint("p", FlushPointReason::kNone);
  EXPECT_EQ(engine.GetProceduralQueue("p").Size(), 2u);
}

// §16.14.6.2: only the pending (not-yet-matured) instances are flushed; an
// instance that already matured stays queued and proceeds to evaluation.
TEST(ProceduralAssertionFlushPoints, MaturedInstancesSurviveFlushPoint) {
  ProceduralAssertionQueue q;
  q.Enqueue(MakePending("matured"));
  q.MatureAll();
  q.Enqueue(MakePending("pending"));
  ASSERT_EQ(q.Size(), 2u);
  ASSERT_EQ(q.MaturedCount(), 1u);

  q.FlushPending();
  EXPECT_EQ(q.Size(), 1u);
  EXPECT_EQ(q.MaturedCount(), 1u);
  EXPECT_EQ(q.Entries().front().instance_name, "matured");
}

// §16.14.6.2: after the queue is flushed, a freshly queued instance with the
// corrected values is queued normally (the a1/b1 example).
TEST(ProceduralAssertionFlushPoints, NewInstanceQueuesNormallyAfterFlush) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("b1");
  q.Enqueue(MakePending("a1"));

  engine.OnProceduralAssertionFlushPoint("b1",
                                         FlushPointReason::kEventControlResume);
  ASSERT_EQ(engine.GetProceduralQueue("b1").Size(), 0u);

  engine.GetProceduralQueue("b1").Enqueue(MakePending("a1"));
  EXPECT_EQ(engine.GetProceduralQueue("b1").Size(), 1u);
}

// §16.14.6.2: flushing a process that has no queued instances is a safe no-op.
TEST(ProceduralAssertionFlushPoints, FlushOnEmptyQueueIsSafeNoOp) {
  SvaEngine engine;
  engine.OnProceduralAssertionFlushPoint("never_queued",
                                         FlushPointReason::kDisableOuterScope);
  EXPECT_EQ(engine.GetProceduralQueue("never_queued").Size(), 0u);
}

// §16.14.6.2: a flush point is reached by a specific process, so it clears only
// that process's pending instances and leaves another process's queue alone.
TEST(ProceduralAssertionFlushPoints, FlushPointAffectsOnlyTheReachingProcess) {
  SvaEngine engine;
  engine.GetProceduralQueue("p_resumed").Enqueue(MakePending("a"));
  engine.GetProceduralQueue("p_other").Enqueue(MakePending("b"));
  engine.GetProceduralQueue("p_other").Enqueue(MakePending("b"));

  engine.OnProceduralAssertionFlushPoint("p_resumed",
                                         FlushPointReason::kEventControlResume);

  EXPECT_EQ(engine.GetProceduralQueue("p_resumed").Size(), 0u);
  EXPECT_EQ(engine.GetProceduralQueue("p_other").Size(), 2u);
}

// §16.14.6.2: when every queued instance has already matured, a flush point
// removes none of them; all matured attempts remain queued.
TEST(ProceduralAssertionFlushPoints, AllMaturedQueueIsUntouchedByFlush) {
  ProceduralAssertionQueue q;
  q.Enqueue(MakePending("m0"));
  q.Enqueue(MakePending("m1"));
  q.MatureAll();
  ASSERT_EQ(q.MaturedCount(), 2u);

  q.FlushPending();
  EXPECT_EQ(q.Size(), 2u);
  EXPECT_EQ(q.MaturedCount(), 2u);
}

}  // namespace
