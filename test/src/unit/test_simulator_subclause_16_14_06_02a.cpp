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

TEST(ProceduralAssertionFlushPoints, WaitResumeIsFlushPoint) {
  EXPECT_TRUE(IsProceduralAssertionFlushPoint(FlushPointReason::kWaitResume));
}

TEST(ProceduralAssertionFlushPoints, AlwaysCombSignalDeltaIsFlushPoint) {
  EXPECT_TRUE(IsProceduralAssertionFlushPoint(
      FlushPointReason::kAlwaysCombSignalDelta));
}

TEST(ProceduralAssertionFlushPoints, AlwaysLatchSignalDeltaIsFlushPoint) {
  EXPECT_TRUE(IsProceduralAssertionFlushPoint(
      FlushPointReason::kAlwaysLatchSignalDelta));
}

TEST(ProceduralAssertionFlushPoints, DisableOuterScopeIsFlushPoint) {
  EXPECT_TRUE(
      IsProceduralAssertionFlushPoint(FlushPointReason::kDisableOuterScope));
}

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

TEST(ProceduralAssertionFlushPoints, NoneReasonDoesNotFlush) {
  SvaEngine engine;
  auto& q = engine.GetProceduralQueue("p");
  q.Enqueue(MakePending("a"));
  q.Enqueue(MakePending("a"));

  engine.OnProceduralAssertionFlushPoint("p", FlushPointReason::kNone);
  EXPECT_EQ(engine.GetProceduralQueue("p").Size(), 2u);
}

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

TEST(ProceduralAssertionFlushPoints, FlushOnEmptyQueueIsSafeNoOp) {
  SvaEngine engine;
  engine.OnProceduralAssertionFlushPoint("never_queued",
                                         FlushPointReason::kDisableOuterScope);
  EXPECT_EQ(engine.GetProceduralQueue("never_queued").Size(), 0u);
}

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
