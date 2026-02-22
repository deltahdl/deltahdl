#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.2.3 Inactive events region
//
// Figure 4-1 shows:
//   region_Active   -> region_Inactive   (forward edge)
//   region_Inactive -> region_Active     (feedback -- iteration)
//   region_Inactive -> pli_region_PreNBA (forward to PreNBA PLI)
//
// The Inactive region is part of the active region set (§4.4.1).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.2.3 Inactive region event execution
// Basic: events scheduled in the Inactive region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4423, InactiveRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kInactive, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.3 Inactive executes after Active
// Inactive events execute only after Active events have drained.
// ---------------------------------------------------------------------------
TEST(SimCh4423, InactiveExecutesAfterActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto *inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() { order.push_back("inactive"); };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  auto *active = sched.GetEventPool().Acquire();
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
}

// ---------------------------------------------------------------------------
// §4.4.2.3 All Active events complete before Inactive
// Multiple Active events all complete before any Inactive event starts.
// ---------------------------------------------------------------------------
TEST(SimCh4423, AllActiveEventsCompleteBeforeInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("active" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  auto *inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() { order.push_back("inactive"); };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  // All three active events come before inactive.
  EXPECT_EQ(order[3], "inactive");
}

// ---------------------------------------------------------------------------
// §4.4.2.3 #0 delay schedules into Inactive
// Simulating #0: an Active callback schedules into Inactive at the same time.
// ---------------------------------------------------------------------------
TEST(SimCh4423, ZeroDelaySchedulesIntoInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto *active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    order.push_back("active");
    // #0 delay: schedule into Inactive at current time.
    auto *delayed = sched.GetEventPool().Acquire();
    delayed->callback = [&order]() { order.push_back("after_zero_delay"); };
    sched.ScheduleEvent({0}, Region::kInactive, delayed);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "after_zero_delay");
}

// ---------------------------------------------------------------------------
// §4.4.2.3 Inactive-to-Active iteration
// Figure 4-1: region_Inactive -> region_Active (feedback edge).
// An Inactive callback that schedules a new Active event triggers
// re-iteration of the active region set.
// ---------------------------------------------------------------------------
TEST(SimCh4423, InactiveToActiveIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Initial Active event schedules into Inactive (#0).
  auto *act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() {
    order.push_back("active1");
    auto *inact = sched.GetEventPool().Acquire();
    inact->callback = [&]() {
      order.push_back("inactive");
      // Inactive schedules new Active event -> triggers re-iteration.
      auto *act2 = sched.GetEventPool().Acquire();
      act2->callback = [&order]() { order.push_back("active2"); };
      sched.ScheduleEvent({0}, Region::kActive, act2);
    };
    sched.ScheduleEvent({0}, Region::kInactive, inact);
  };
  sched.ScheduleEvent({0}, Region::kActive, act1);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active1");
  EXPECT_EQ(order[1], "inactive");
  EXPECT_EQ(order[2], "active2");
}

// ---------------------------------------------------------------------------
// §4.4.2.3 Multiple #0 delays: chained zero-delay scheduling.
// Active -> Inactive -> Active -> Inactive demonstrates repeated iteration.
// ---------------------------------------------------------------------------
TEST(SimCh4423, ChainedZeroDelayIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Inner chain: active2 -> inactive2.
  auto log_inactive2 = [&order]() { order.push_back("inactive2"); };
  auto do_active2 = [&]() {
    order.push_back("active2");
    auto *inact2 = sched.GetEventPool().Acquire();
    inact2->callback = log_inactive2;
    sched.ScheduleEvent({0}, Region::kInactive, inact2);
  };
  // Outer chain: active1 -> inactive1 -> (inner chain).
  auto do_inactive1 = [&]() {
    order.push_back("inactive1");
    auto *act2 = sched.GetEventPool().Acquire();
    act2->callback = do_active2;
    sched.ScheduleEvent({0}, Region::kActive, act2);
  };

  auto *act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() {
    order.push_back("active1");
    auto *inact1 = sched.GetEventPool().Acquire();
    inact1->callback = do_inactive1;
    sched.ScheduleEvent({0}, Region::kInactive, inact1);
  };
  sched.ScheduleEvent({0}, Region::kActive, act1);

  sched.Run();
  std::vector<std::string> expected = {"active1", "inactive1", "active2",
                                       "inactive2"};
  EXPECT_EQ(order, expected);
}

// ---------------------------------------------------------------------------
// §4.4.2.3 Inactive is part of the active region set (§4.4.1).
// Its ordinal lies between Active and PostNBA.
// ---------------------------------------------------------------------------
TEST(SimCh4423, InactiveIsWithinActiveRegionSet) {
  auto inactive_ord = static_cast<int>(Region::kInactive);
  auto active_ord = static_cast<int>(Region::kActive);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  EXPECT_GT(inactive_ord, active_ord);
  EXPECT_LT(inactive_ord, post_nba_ord);
}

// ---------------------------------------------------------------------------
// §4.4.2.3 Figure 4-1: region_Inactive -> pli_region_PreNBA.
// After Inactive drains and no feedback to Active, the flow proceeds
// to PreNBA/NBA.  This test verifies Inactive executes before NBA.
// ---------------------------------------------------------------------------
TEST(SimCh4423, InactiveExecutesBeforeNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto *nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto *inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() { order.push_back("inactive"); };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "inactive");
  EXPECT_EQ(order[1], "nba");
}

// ---------------------------------------------------------------------------
// §4.4.2.3 Inactive events across multiple time slots.
// Each time slot has its own Inactive region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4423, InactiveEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kInactive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.2.3 Multiple Inactive events coexist and all execute.
// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// §4.4.2.3 Inactive vs Re-Inactive ordering
// A #0 delay in the active context goes to kInactive; in the reactive
// context it goes to kReInactive.  Inactive (active set) executes before
// Re-Inactive (reactive set).
// ---------------------------------------------------------------------------
TEST(SimCh4423, InactiveExecutesBeforeReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto *ev_inactive = sched.GetEventPool().Acquire();
  ev_inactive->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({0}, Region::kInactive, ev_inactive);

  auto *ev_reinactive = sched.GetEventPool().Acquire();
  ev_reinactive->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({0}, Region::kReInactive, ev_reinactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

// ---------------------------------------------------------------------------
// §4.4.2.3 Multiple Inactive events coexist and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4423, InactiveRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kInactive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}
