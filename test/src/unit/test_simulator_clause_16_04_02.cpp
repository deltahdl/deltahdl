#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

struct FlushPointFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

TEST(DeferredFlushPoints, EventControlResumeIsFlushPoint) {
  EXPECT_TRUE(IsDeferredFlushPoint(FlushPointReason::kEventControlResume));
}

TEST(DeferredFlushPoints, WaitResumeIsFlushPoint) {
  EXPECT_TRUE(IsDeferredFlushPoint(FlushPointReason::kWaitResume));
}

TEST(DeferredFlushPoints, AlwaysCombSignalDeltaIsFlushPoint) {
  EXPECT_TRUE(IsDeferredFlushPoint(FlushPointReason::kAlwaysCombSignalDelta));
}

TEST(DeferredFlushPoints, AlwaysLatchSignalDeltaIsFlushPoint) {
  EXPECT_TRUE(IsDeferredFlushPoint(FlushPointReason::kAlwaysLatchSignalDelta));
}

TEST(DeferredFlushPoints, DisableOuterScopeIsFlushPoint) {
  EXPECT_TRUE(IsDeferredFlushPoint(FlushPointReason::kDisableOuterScope));
}

TEST(DeferredFlushPoints, NoneIsNotAFlushPoint) {
  EXPECT_FALSE(IsDeferredFlushPoint(FlushPointReason::kNone));
}

TEST(DeferredFlushPoints, EventResumeClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kEventControlResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredFlushPoints, WaitResumeClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 0;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kWaitResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredFlushPoints, AlwaysCombSignalDeltaClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 0;
  f.engine.QueuePendingReport("alc", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("alc",
                                FlushPointReason::kAlwaysCombSignalDelta);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("alc").Size(), 0u);
}

TEST(DeferredFlushPoints, AlwaysLatchSignalDeltaClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("alt", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("alt",
                                FlushPointReason::kAlwaysLatchSignalDelta);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("alt").Size(), 0u);
}

TEST(DeferredFlushPoints, DisableOuterScopeClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kDisableOuterScope);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredFlushPoints, NoneReasonDoesNotClearQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kNone);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

TEST(DeferredFlushPoints, FlushOnEmptyQueueIsSafeNoOp) {
  FlushPointFixture f;
  f.engine.OnDeferredFlushPoint("nonexistent",
                                FlushPointReason::kDisableOuterScope);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("nonexistent").Size(), 0u);
}

}  // namespace
