#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.2.2 Active events region
//
// Figure 4-1 shows:
//   region_Active -> region_Active   (self-loop)
//   region_Active -> region_Inactive (forward edge)
//   Multiple incoming edges from PLI/other regions feed into Active.
//
// The Active region is the core evaluation region of the active region
// set (§4.4.1).  All primary simulation activity occurs here.
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.2.2 Active region event execution
// Basic: events scheduled in the Active region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.2 Active region holds multiple events
// Multiple events coexist in the Active region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.2.2 Active events processed in any valid order
// Any ordering of Active events is permitted.  Our FIFO implementation
// is one valid ordering.  This test verifies that all events execute
// regardless of insertion order.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveEventsProcessedInAnyValidOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 4; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  // All four events executed — any permutation is valid per LRM.
  std::vector<int> sorted = order;
  std::sort(sorted.begin(), sorted.end());
  EXPECT_EQ(sorted, (std::vector<int>{0, 1, 2, 3}));
}

// ---------------------------------------------------------------------------
// §4.4.2.2 + Figure 4-1: region_Active -> region_Active (self-loop).
// An Active callback can schedule more Active events in the same time
// slot, and they will be evaluated within the same iteration.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveSelfLoopSchedulesMoreActiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // First Active callback schedules a second Active event.
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    order.push_back(1);
    auto* next = sched.GetEventPool().Acquire();
    next->callback = [&order]() { order.push_back(2); };
    sched.ScheduleEvent({0}, Region::kActive, next);
  };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

// ---------------------------------------------------------------------------
// §4.4.2.2 + Figure 4-1: region_Active -> region_Inactive.
// Active events complete before Inactive events begin within the same
// active region set iteration.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveExecutesBeforeInactive) {
  VerifyTwoRegionOrder(Region::kActive, "active", Region::kInactive,
                       "inactive");
}

// ---------------------------------------------------------------------------
// §4.4.2.2 Active is part of the active region set (§4.4.1).
// Its ordinal lies between PreActive and PostNBA.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveIsWithinActiveRegionSet) {
  auto active_ord = static_cast<int>(Region::kActive);
  auto pre_active_ord = static_cast<int>(Region::kPreActive);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  EXPECT_GT(active_ord, pre_active_ord);
  EXPECT_LT(active_ord, post_nba_ord);
}

// ---------------------------------------------------------------------------
// §4.4.2.2 Active executes after Preponed and PreActive per Figure 4-1.
// The flow is: Preponed -> PreActive -> Active.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveExecutesAfterPreponedAndPreActive) {
  VerifyThreeRegionOrder(Region::kPreponed, "preponed", Region::kPreActive,
                         "preactive", Region::kActive, "active");
}

// ---------------------------------------------------------------------------
// §4.4.2.2 Active region events across multiple time slots.
// Each time slot has its own Active region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kActive);
}

// ---------------------------------------------------------------------------
// §4.4.2.2 + §4.5 iteration: NBA events cause Active set re-iteration.
// After NBA drains, if new Active events appear, the active set iterates
// again — Active region participates in this iteration loop.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveParticipatesInNBAIteration) {
  VerifyIterationChain(Region::kActive, "active", Region::kNBA, "nba");
}

// ---------------------------------------------------------------------------
// §4.4.2.2 + Figure 4-1: Reactive-to-Active restart.
// When Reactive schedules an Active event, the active set restarts.
// Active region is the target of this restart path.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveRestartsFromReactiveRegion) {
  VerifyRegionRestart(Region::kActive, "active1", Region::kReactive, "reactive",
                      Region::kActive, "active2");
}
