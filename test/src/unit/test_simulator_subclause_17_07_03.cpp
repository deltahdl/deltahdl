#include <gtest/gtest.h>

#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/checker_scheduling_semantics.h"
#include "simulator/scheduler.h"

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
  const Region kReNba = HomeRegionForCheckerStatement(
      CheckerStatementKind::kCheckerVariableNonblocking);
  VerifyThreeRegionOrder({Region::kReactive, "reactive"},
                         {Region::kReInactive, "reinactive"},
                         {kReNba, "renba"});
}

// §17.7.3: these scheduling rules make possible assignment of sequence end
// point values to checker variables. In `always_ff @clk a <= s.triggered;` the
// right-hand side is captured by the blocking evaluation in the Reactive region
// while the update to checker variable `a` is scheduled in the Re-NBA region,
// so the end point value is available when the update is applied.
TEST(CheckerSchedulingSemantics, SequenceEndPointCaptureSpansReactiveToReNBA) {
  const Region kRhsEval =
      HomeRegionForCheckerStatement(CheckerStatementKind::kBlocking);
  const Region kVarUpdate = HomeRegionForCheckerStatement(
      CheckerStatementKind::kCheckerVariableNonblocking);
  EXPECT_EQ(kRhsEval, Region::kReactive);
  EXPECT_EQ(kVarUpdate, Region::kReNBA);
  EXPECT_NE(kRhsEval, kVarUpdate);
}

// §17.7.3: concurrent assertions have invariant scheduling semantics whether
// present in checker code or design code — the region is the same in both
// contexts, for *every* region, not just a sampled few.
// A concurrent assertion scheduled in any design-code region (e.g., Active,
// NBA, Observed, Postponed) keeps that same region when it appears in a
// checker, so the production mapping must be the identity across the entire
// region domain.
TEST(CheckerSchedulingSemantics,
     ConcurrentAssertionSchedulingInvariantAcrossAllRegions) {
  for (int i = 0; i < static_cast<int>(Region::kCOUNT); ++i) {
    const auto kR = static_cast<Region>(i);
    EXPECT_EQ(ConcurrentAssertionRegionInChecker(kR), kR);
  }
}

// §17.7.3: the phrase "similarly to programs, see 24.3.1" is normative — a
// checker's change-sensitive/blocking statements do not merely happen to land
// in the Reactive region, they land there because they use the *same* placement
// the program-reactive path applies. Observe that the checker mapping is the
// identical scheduler production, not an independently chosen constant, so the
// two can never drift.
TEST(CheckerSchedulingSemantics,
     BlockingPlacementReusesProgramReactiveMapping) {
  EXPECT_EQ(HomeRegionForCheckerStatement(CheckerStatementKind::kBlocking),
            Scheduler::HomeRegionForReactiveBlockingAssign());
  EXPECT_EQ(
      HomeRegionForCheckerStatement(CheckerStatementKind::kChangeSensitive),
      Scheduler::HomeRegionForReactiveBlockingAssign());
}

// §17.7.3: a checker-variable nonblocking update schedules in Re-NBA. That
// region is the reactive-set dual of the ordinary NBA region — the same mapping
// the program path uses when a nonblocking assignment runs in a reactive
// context. Observe the checker rule is derived from that shared dual, not a
// standalone Re-NBA literal.
TEST(CheckerSchedulingSemantics,
     CheckerVariableNonblockingReusesReactiveNBADual) {
  EXPECT_EQ(HomeRegionForCheckerStatement(
                CheckerStatementKind::kCheckerVariableNonblocking),
            Scheduler::ReactiveSetDualOf(Region::kNBA));
}

}  // namespace
