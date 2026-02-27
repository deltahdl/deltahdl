#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

#include "helpers_scheduler_event.h"

using namespace delta;

// ===========================================================================
// §4.4.2.6 Reactive events region
//
// Figure 4-1 shows:
//   pli_region_PostObserved -> region_Reactive  (forward from PostObserved)
//   region_Reactive -> region_Reactive          (self-loop -- any order)
//   region_Reactive -> region_ReInactive        (forward to Re-Inactive)
//   pli_region_PostReNBA -> region_Reactive     (feedback from PostReNBA)
//   pli_region_PreReNBA -> region_Reactive      (feedback from PreReNBA)
//
// The Reactive region is the core evaluation region of the reactive region
// set (§4.4.1), dual to Active in the active region set.
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.2.6 Reactive region event execution
// Basic: events scheduled in the Reactive region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kReactive, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.6 Reactive region holds multiple events
// Multiple events coexist in the Reactive region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.2.6 Reactive events processed in any valid order
// Any ordering of Reactive events is permitted.  Our FIFO implementation
// is one valid ordering.  This test verifies that all events execute
// regardless of insertion order.
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveEventsProcessedInAnyValidOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 4; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  // All four events executed — any permutation is valid per LRM.
  std::vector<int> sorted = order;
  std::sort(sorted.begin(), sorted.end());
  EXPECT_EQ(sorted, (std::vector<int>{0, 1, 2, 3}));
}

// ---------------------------------------------------------------------------
// §4.4.2.6 + Figure 4-1: region_Reactive -> region_Reactive (self-loop).
// A Reactive callback can schedule more Reactive events in the same time
// slot, and they will be evaluated within the same iteration.
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveSelfLoopSchedulesMoreReactiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // First Reactive callback schedules a second Reactive event.
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    order.push_back(1);
    auto* next = sched.GetEventPool().Acquire();
    next->callback = [&order]() { order.push_back(2); };
    sched.ScheduleEvent({0}, Region::kReactive, next);
  };
  sched.ScheduleEvent({0}, Region::kReactive, ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

// ---------------------------------------------------------------------------
// §4.4.2.6 + Figure 4-1: region_Reactive -> region_ReInactive.
// Reactive events complete before Re-Inactive events begin within the
// same reactive region set iteration.
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveExecutesBeforeReInactive) {
  VerifyTwoRegionOrder(Region::kReactive, "reactive", Region::kReInactive,
                       "reinactive");
}

// ---------------------------------------------------------------------------
// §4.4.2.6 Reactive is dual of Active (within reactive region set)
// Its ordinal lies between PostObserved and PrePostponed -- within the
// reactive region set.
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveIsWithinReactiveRegionSet) {
  auto reactive_ord = static_cast<int>(Region::kReactive);
  auto post_observed_ord = static_cast<int>(Region::kPostObserved);
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  EXPECT_GT(reactive_ord, post_observed_ord);
  EXPECT_LT(reactive_ord, pre_postponed_ord);
}

// ---------------------------------------------------------------------------
// §4.4.2.6 Reactive executes after Observed and PostObserved per
// Figure 4-1.  The flow is: Observed -> PostObserved -> Reactive.
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveExecutesAfterObservedAndPostObserved) {
  VerifyThreeRegionOrder(Region::kObserved, "observed", Region::kPostObserved,
                         "post_observed", Region::kReactive, "reactive");
}

// ---------------------------------------------------------------------------
// §4.4.2.6 Reactive region events across multiple time slots.
// Each time slot has its own Reactive region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kReactive);
}

// ---------------------------------------------------------------------------
// §4.4.2.6 + §4.5 iteration: Re-NBA events cause Reactive set
// re-iteration.  After Re-NBA drains, if new Reactive events appear,
// the reactive set iterates again — dual of NBA->Active iteration.
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveParticipatesInReNBAIteration) {
  VerifyIterationChain(Region::kReactive, "reactive", Region::kReNBA, "renba");
}

// ---------------------------------------------------------------------------
// §4.4.2.6 Reactive-to-Active restart
// When a Reactive callback schedules an Active event, the active set
// restarts (per Figure 4-1 feedback).
// ---------------------------------------------------------------------------
TEST(SimCh4426, ReactiveSchedulesActiveRestart) {
  VerifyRegionRestart(Region::kActive, "active1", Region::kReactive, "reactive",
                      Region::kActive, "active2");
}
