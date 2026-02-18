#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

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
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() { order.push_back("inactive"); };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
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
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering, not insertion order.
  schedule(Region::kActive, "active");
  schedule(Region::kPreActive, "preactive");
  schedule(Region::kPreponed, "preponed");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "preponed");
  EXPECT_EQ(order[1], "preactive");
  EXPECT_EQ(order[2], "active");
}

// ---------------------------------------------------------------------------
// §4.4.2.2 Active region events across multiple time slots.
// Each time slot has its own Active region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.2.2 + §4.5 iteration: NBA events cause Active set re-iteration.
// After NBA drains, if new Active events appear, the active set iterates
// again — Active region participates in this iteration loop.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveParticipatesInNBAIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Initial Active event schedules an NBA.
  auto* act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() {
    order.push_back("active1");
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&]() {
      order.push_back("nba");
      // NBA schedules a new Active event -> triggers re-iteration.
      auto* act2 = sched.GetEventPool().Acquire();
      act2->callback = [&order]() { order.push_back("active2"); };
      sched.ScheduleEvent({0}, Region::kActive, act2);
    };
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, act1);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active1");
  EXPECT_EQ(order[1], "nba");
  EXPECT_EQ(order[2], "active2");
}

// ---------------------------------------------------------------------------
// §4.4.2.2 + Figure 4-1: Reactive-to-Active restart.
// When Reactive schedules an Active event, the active set restarts.
// Active region is the target of this restart path.
// ---------------------------------------------------------------------------
TEST(SimCh4422, ActiveRestartsFromReactiveRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* act1 = sched.GetEventPool().Acquire();
  act1->callback = [&order]() { order.push_back("active1"); };
  sched.ScheduleEvent({0}, Region::kActive, act1);

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    auto* act2 = sched.GetEventPool().Acquire();
    act2->callback = [&order]() { order.push_back("active2"); };
    sched.ScheduleEvent({0}, Region::kActive, act2);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active1");
  EXPECT_EQ(order[1], "reactive");
  EXPECT_EQ(order[2], "active2");
}
