#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.3 Pre-NBA PLI region
//
// Figure 4-1 shows:
//   region_Inactive -> pli_region_PreNBA -> region_NBA
//
// The Pre-NBA region is a read-write PLI callback control point.
// Pre-NBA is part of the active region set (§4.4.1).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.3 Pre-NBA PLI callback control point
// Basic: events scheduled in the Pre-NBA region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBARegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPreNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.3 Pre-NBA can read values
// A Pre-NBA callback can read state set during initialization.
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBACanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 42;
  int sampled = -1;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreNBA, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.3 Pre-NBA can write values
// A Pre-NBA callback can modify state that NBA will later observe.
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBACanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_nba = -1;

  // Pre-NBA writes a value.
  auto* pre_nba = sched.GetEventPool().Acquire();
  pre_nba->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre_nba);

  // NBA reads the value — should see 99.
  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { sampled_in_nba = value; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  EXPECT_EQ(sampled_in_nba, 99);
}

// ---------------------------------------------------------------------------
// §4.4.3.3 Pre-NBA can create events
// A Pre-NBA callback can schedule new events (e.g., into NBA).
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBACanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_nba = sched.GetEventPool().Acquire();
  pre_nba->callback = [&]() {
    order.push_back("pre_nba");
    // Create an event in the NBA region from Pre-NBA.
    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_nba"); };
    sched.ScheduleEvent({0}, Region::kNBA, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_nba");
  EXPECT_EQ(order[1], "created_nba");
}

// ---------------------------------------------------------------------------
// §4.4.3.3 Pre-NBA executes before NBA
// Pre-NBA executes before NBA in the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBAExecutesBeforeNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule NBA first, then Pre-NBA — ordering must still hold.
  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* pre_nba = sched.GetEventPool().Acquire();
  pre_nba->callback = [&]() { order.push_back("pre_nba"); };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_nba");
  EXPECT_EQ(order[1], "nba");
}

// ---------------------------------------------------------------------------
// §4.4.3.3 + Figure 4-1: Inactive -> Pre-NBA -> NBA.
// Pre-NBA executes after Inactive and before NBA.
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBAExecutesAfterInactiveBeforeNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering.
  schedule(Region::kNBA, "nba");
  schedule(Region::kPreNBA, "pre_nba");
  schedule(Region::kInactive, "inactive");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "inactive");
  EXPECT_EQ(order[1], "pre_nba");
  EXPECT_EQ(order[2], "nba");
}

// ---------------------------------------------------------------------------
// §4.4.3.3 Pre-NBA is part of the active region set (§4.4.1).
// Its ordinal lies between Inactive and NBA.
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBAIsWithinActiveRegionSet) {
  auto pre_nba_ord = static_cast<int>(Region::kPreNBA);
  auto inactive_ord = static_cast<int>(Region::kInactive);
  auto nba_ord = static_cast<int>(Region::kNBA);
  EXPECT_GT(pre_nba_ord, inactive_ord);
  EXPECT_LT(pre_nba_ord, nba_ord);
}

// ---------------------------------------------------------------------------
// §4.4.3.3 Multiple Pre-NBA callbacks
// Multiple PLI callbacks coexist in the Pre-NBA region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBARegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.3 Pre-NBA events across multiple time slots.
// Each time slot has its own Pre-NBA region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBAEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.3 Pre-NBA read-write capability
// Pre-NBA is read-write. A Pre-NBA callback writes state that Active set
// earlier; NBA then sees the Pre-NBA modification. This verifies read-write
// capability in the context of the full active region set ordering.
// ---------------------------------------------------------------------------
TEST(SimCh4433, PreNBAReadWriteInActiveRegionSetContext) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int active_sample = -1;
  int nba_sample = -1;

  // Active writes value = 10.
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Pre-NBA reads the Active-set value and overwrites it to 55.
  auto* pre_nba = sched.GetEventPool().Acquire();
  pre_nba->callback = [&]() {
    active_sample = value;
    value = 55;
  };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre_nba);

  // NBA samples value — should see 55 from Pre-NBA.
  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { nba_sample = value; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  EXPECT_EQ(active_sample, 10);
  EXPECT_EQ(nba_sample, 55);
}
