#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

#include "helpers_scheduler_event.h"

using namespace delta;

// ===========================================================================
// §4.4.2.4 NBA events region
//
// Figure 4-1 shows:
//   pli_region_PreNBA -> region_NBA    (forward from PreNBA PLI)
//   region_NBA -> pli_region_PostNBA   (forward to PostNBA PLI)
//   region_NBA -> region_Active        (feedback -- re-iteration)
//
// The NBA region is part of the active region set (§4.4.1).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.2.4 NBA region event execution
// Basic: events scheduled in the NBA region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4424, NBARegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.4 NBA executes after Inactive
// NBA events execute only after Inactive events have drained.
// ---------------------------------------------------------------------------
TEST(SimCh4424, NBAExecutesAfterInactive) {
  VerifyTwoRegionOrder(Region::kInactive, "inactive", Region::kNBA, "nba");
}

// ---------------------------------------------------------------------------
// §4.4.2.4 All Inactive events complete before NBA
// Multiple Inactive events all complete before any NBA event starts.
// ---------------------------------------------------------------------------
TEST(SimCh4424, AllInactiveEventsCompleteBeforeNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("inactive" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kInactive, ev);
  }

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  // All three Inactive events come before NBA.
  EXPECT_EQ(order[3], "nba");
}

// ---------------------------------------------------------------------------
// §4.4.2.4 Nonblocking assignment schedules NBA at current time
// An Active callback schedules into NBA at the same time (current time).
// ---------------------------------------------------------------------------
TEST(SimCh4424, NonblockingAssignmentSchedulesNBACurrentTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    order.push_back("active");
    // Nonblocking assignment: schedule NBA at current time.
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&order]() { order.push_back("nba"); };
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
}

// ---------------------------------------------------------------------------
// §4.4.2.4 Nonblocking assignment schedules NBA at later time
// An Active callback at time 0 schedules an NBA event at time 5.
// ---------------------------------------------------------------------------
TEST(SimCh4424, NonblockingAssignmentSchedulesNBALaterTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> nba_times;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    // Nonblocking assignment with delay: schedule NBA at a later time.
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&nba_times, &sched]() {
      nba_times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({5}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(nba_times.size(), 1u);
  EXPECT_EQ(nba_times[0], 5u);
}

// ---------------------------------------------------------------------------
// §4.4.2.4 + Figure 4-1: region_NBA -> region_Active (feedback edge).
// An NBA callback that schedules a new Active event triggers
// re-iteration of the active region set.
// ---------------------------------------------------------------------------
TEST(SimCh4424, NBAToActiveIteration) {
  VerifyIterationChain(Region::kActive, "active", Region::kNBA, "nba");
}

// ---------------------------------------------------------------------------
// §4.4.2.4 NBA region executes after Active and Inactive, before Observed.
// This confirms its position in the region ordering per §4.4.2.
// ---------------------------------------------------------------------------
TEST(SimCh4424, NBAExecutesAfterActiveAndInactiveBeforeObserved) {
  VerifyFourRegionOrder(Region::kActive, "active", Region::kInactive, "inactive",
                        Region::kNBA, "nba", Region::kObserved, "observed");
}

// ---------------------------------------------------------------------------
// §4.4.2.4 NBA is part of the active region set (§4.4.1).
// Its ordinal lies between Inactive and PostNBA.
// ---------------------------------------------------------------------------
TEST(SimCh4424, NBAIsWithinActiveRegionSet) {
  auto nba_ord = static_cast<int>(Region::kNBA);
  auto inactive_ord = static_cast<int>(Region::kInactive);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  EXPECT_GT(nba_ord, inactive_ord);
  EXPECT_LT(nba_ord, post_nba_ord);
}

// ---------------------------------------------------------------------------
// §4.4.2.4 NBA events across multiple time slots.
// Each time slot has its own NBA region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4424, NBAEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kNBA);
}

// ---------------------------------------------------------------------------
// §4.4.2.4 Multiple NBA events coexist and all execute.
// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// §4.4.2.4 NBA vs Re-NBA ordering
// NBA in the active context goes to kNBA; in the reactive context it goes
// to kReNBA.  NBA (active set) executes before Re-NBA (reactive set).
// ---------------------------------------------------------------------------
TEST(SimCh4424, NBAExecutesBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev_nba = sched.GetEventPool().Acquire();
  ev_nba->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({0}, Region::kNBA, ev_nba);

  auto* ev_renba = sched.GetEventPool().Acquire();
  ev_renba->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({0}, Region::kReNBA, ev_renba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

// ---------------------------------------------------------------------------
// §4.4.2.4 Multiple NBA events coexist and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4424, NBARegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}
