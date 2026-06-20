#include <gtest/gtest.h>

#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/checker_scheduling_semantics.h"

using namespace delta;

namespace {

// §17.7.3: change-sensitive constructs of a checker (clocking events,
// continuous assignments) are scheduled in the Reactive region.
TEST(CheckerSchedulingSemantics, ChangeSensitiveConstructsAreReactive) {
  EXPECT_EQ(
      HomeRegionForCheckerStatement(CheckerStatementKind::kChangeSensitive),
      Region::kReactive);
}

// §17.7.3: all blocking statements of a checker are scheduled in the Reactive
// region.
TEST(CheckerSchedulingSemantics, BlockingStatementsAreReactive) {
  EXPECT_EQ(HomeRegionForCheckerStatement(CheckerStatementKind::kBlocking),
            Region::kReactive);
}

// §17.7.3: the nonblocking assignments of checker variables schedule their
// updates in the Re-NBA region.
TEST(CheckerSchedulingSemantics, CheckerVariableNonblockingUpdatesAreReNBA) {
  EXPECT_EQ(HomeRegionForCheckerStatement(
                CheckerStatementKind::kCheckerVariableNonblocking),
            Region::kReNBA);
}

// §17.7.3: the Re-NBA region is processed only after the Reactive and
// Re-Inactive regions have been emptied of events. Using the region the
// production helper assigns to a checker-variable nonblocking update, observe
// that the scheduler drains Reactive and Re-Inactive before it.
TEST(CheckerSchedulingSemantics, ReNBAIsProcessedAfterReactiveAndReInactive) {
  const Region re_nba = HomeRegionForCheckerStatement(
      CheckerStatementKind::kCheckerVariableNonblocking);
  VerifyThreeRegionOrder({Region::kReactive, "reactive"},
                         {Region::kReInactive, "reinactive"},
                         {re_nba, "renba"});
}

// §17.7.3: these scheduling rules make possible assignment of sequence end
// point values to checker variables. In `always_ff @clk a <= s.triggered;` the
// right-hand side is captured by the blocking evaluation in the Reactive region
// while the update to checker variable `a` is scheduled in the Re-NBA region,
// so the end point value is available when the update is applied.
TEST(CheckerSchedulingSemantics, SequenceEndPointCaptureSpansReactiveToReNBA) {
  const Region rhs_eval =
      HomeRegionForCheckerStatement(CheckerStatementKind::kBlocking);
  const Region var_update = HomeRegionForCheckerStatement(
      CheckerStatementKind::kCheckerVariableNonblocking);
  EXPECT_EQ(rhs_eval, Region::kReactive);
  EXPECT_EQ(var_update, Region::kReNBA);
  EXPECT_NE(rhs_eval, var_update);
}

// §17.7.3: concurrent assertions have invariant scheduling semantics whether
// present in checker code or design code — the region is the same in both
// contexts, regardless of which region a given assertion uses.
TEST(CheckerSchedulingSemantics, ConcurrentAssertionSchedulingIsInvariant) {
  for (Region r : {Region::kObserved, Region::kReactive, Region::kReNBA}) {
    EXPECT_EQ(ConcurrentAssertionRegionInChecker(r), r);
  }
}

// §17.7.3: the invariance holds for *every* region, not just a sampled few.
// A concurrent assertion scheduled in any design-code region (e.g., Active,
// NBA, Observed, Postponed) keeps that same region when it appears in a
// checker, so the production mapping must be the identity across the entire
// region domain.
TEST(CheckerSchedulingSemantics,
     ConcurrentAssertionSchedulingInvariantAcrossAllRegions) {
  for (int i = 0; i < static_cast<int>(Region::kCOUNT); ++i) {
    const Region r = static_cast<Region>(i);
    EXPECT_EQ(ConcurrentAssertionRegionInChecker(r), r);
  }
}

}  // namespace
