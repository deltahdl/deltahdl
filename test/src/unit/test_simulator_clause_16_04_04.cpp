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

struct DeferredDisableFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;

  void QueueObserved(std::string_view process_id, std::string_view instance) {
    DeferredAssertion da;
    da.condition_val = 0;
    da.instance_name = std::string(instance);
    engine.QueuePendingReport(process_id, da, DeferralKind::kObserved);
  }
};

// §16.4.4: disabling a specific deferred assertion, or the outermost scope of a
// procedure with an active deferred report queue, clears pending reports;
// disabling a task or a non-outermost scope does not.
TEST(DeferredDisableClassification, SpecificAssertionFlushes) {
  EXPECT_TRUE(
      DisableFlushesDeferredAssertions(DisableTarget::kSpecificAssertion));
}

TEST(DeferredDisableClassification, OutermostScopeFlushes) {
  EXPECT_TRUE(DisableFlushesDeferredAssertions(DisableTarget::kOutermostScope));
}

TEST(DeferredDisableClassification, TaskDoesNotFlush) {
  EXPECT_FALSE(DisableFlushesDeferredAssertions(DisableTarget::kTask));
}

TEST(DeferredDisableClassification, NonOutermostScopeDoesNotFlush) {
  EXPECT_FALSE(
      DisableFlushesDeferredAssertions(DisableTarget::kNonOutermostScope));
}

// §16.4.4 Claim A: disabling a specific deferred assertion cancels the pending
// reports for that assertion only, leaving other assertions' reports queued.
TEST(DeferredDisableSpecific, CancelsOnlyNamedAssertionPendingReports) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
  EXPECT_EQ(
      f.engine.GetDeferredReportQueue("p0").Entries().front().da.instance_name,
      "a2");
}

// §16.4.4 Claim A: a report that already matured is no longer pending, so
// disabling its assertion does not remove it.
TEST(DeferredDisableSpecific, LeavesMaturedReportOfNamedAssertion) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.engine.MatureObservedReports("p0");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 1u);

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

// §16.4.4 Claim B: disabling the outermost scope flushes the whole pending
// report queue of the process.
TEST(DeferredDisableOutermost, FlushesAllPendingReports) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

// §16.4.4 Claim B: only pending (non-matured) reports are cleared; a matured
// report survives an outermost-scope disable.
TEST(DeferredDisableOutermost, LeavesMaturedReports) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.engine.MatureObservedReports("p0");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 1u);
}

// §16.4.4 Claim C: disabling a task does not flush any pending reports.
TEST(DeferredDisableNoFlush, TaskLeavesQueueIntact) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");

  f.engine.ApplyDisableToDeferredAssertions("p0", DisableTarget::kTask, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

// §16.4.4 Claim C: disabling a non-outermost scope does not flush any pending
// reports.
TEST(DeferredDisableNoFlush, NonOutermostScopeLeavesQueueIntact) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kNonOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

// §16.4.4 Claim A, edge case: naming an assertion that has no pending reports
// leaves the queue untouched.
TEST(DeferredDisableSpecific, UnknownAssertionNameLeavesQueueIntact) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "missing");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

// §16.4.4 Claim A, edge case: every pending report of the named assertion is
// cancelled, even when the same assertion queued several reports.
TEST(DeferredDisableSpecific, CancelsAllPendingReportsOfSameAssertion) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 3u);

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
  EXPECT_EQ(
      f.engine.GetDeferredReportQueue("p0").Entries().front().da.instance_name,
      "a2");
}

// §16.4.4 Claim A, edge case: deferred reports are per process, so disabling a
// specific assertion in one process does not touch another process's queue.
TEST(DeferredDisableSpecific, DoesNotAffectOtherProcessQueue) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p1", "a1");

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p1").Size(), 1u);
}

// §16.4.4 Claim B, edge case: an outermost-scope disable on a process with no
// pending reports is a safe no-op.
TEST(DeferredDisableOutermost, EmptyQueueIsSafeNoOp) {
  DeferredDisableFixture f;

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

// §16.4.4 Claim B, edge case: when every report has already matured, an
// outermost-scope disable clears nothing.
TEST(DeferredDisableOutermost, AllMaturedQueueSurvives) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  f.engine.MatureObservedReports("p0");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 2u);

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

// §16.4.4 Claim B, edge case: an outermost-scope disable of one process leaves
// another process's pending reports in place.
TEST(DeferredDisableOutermost, DoesNotAffectOtherProcessQueue) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p1", "a1");

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p1").Size(), 1u);
}

}  // namespace
