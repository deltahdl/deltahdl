#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.7 Pre-Re-NBA PLI region
//
// LRM §4.4.3.7:
//   "The Pre-Re-NBA region provides for a PLI callback control point that
//    allows PLI application routines to read and write values and create
//    events before the events in the Re-NBA region are evaluated (see 4.5)."
//
// Figure 4-1 shows:
//   region_ReInactive -> pli_region_PreReNBA -> region_ReNBA
//
// The Pre-Re-NBA region is a read-write PLI callback control point.
// Pre-Re-NBA is part of the reactive region set (§4.4.1 iterative regions).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.7 "provides for a PLI callback control point"
// Basic: events scheduled in the Pre-Re-NBA region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBARegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPreReNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.7 "allows PLI application routines to read ... values"
// A Pre-Re-NBA callback can read state set by an earlier region.
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBACanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Reactive sets value = 42.
  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  // Pre-Re-NBA reads value — should see 42.
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreReNBA, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.7 "allows PLI application routines to ... write values"
// A Pre-Re-NBA callback can modify state that Re-NBA will later observe.
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBACanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_re_nba = -1;

  // Pre-Re-NBA writes a value.
  auto* pre_re_nba = sched.GetEventPool().Acquire();
  pre_re_nba->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPreReNBA, pre_re_nba);

  // Re-NBA reads the value — should see 99.
  auto* re_nba = sched.GetEventPool().Acquire();
  re_nba->callback = [&]() { sampled_in_re_nba = value; };
  sched.ScheduleEvent({0}, Region::kReNBA, re_nba);

  sched.Run();
  EXPECT_EQ(sampled_in_re_nba, 99);
}

// ---------------------------------------------------------------------------
// §4.4.3.7 "allows PLI application routines to ... create events"
// A Pre-Re-NBA callback can schedule new events (e.g., into Re-NBA).
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBACanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_re_nba = sched.GetEventPool().Acquire();
  pre_re_nba->callback = [&]() {
    order.push_back("pre_re_nba");
    // Create an event in the Re-NBA region from Pre-Re-NBA.
    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_re_nba"); };
    sched.ScheduleEvent({0}, Region::kReNBA, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPreReNBA, pre_re_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_re_nba");
  EXPECT_EQ(order[1], "created_re_nba");
}

// ---------------------------------------------------------------------------
// §4.4.3.7 "before the events in the Re-NBA region are evaluated"
// Pre-Re-NBA executes before Re-NBA in the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBAExecutesBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule Re-NBA first, then Pre-Re-NBA — ordering must still hold.
  auto* re_nba = sched.GetEventPool().Acquire();
  re_nba->callback = [&]() { order.push_back("re_nba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, re_nba);

  auto* pre_re_nba = sched.GetEventPool().Acquire();
  pre_re_nba->callback = [&]() { order.push_back("pre_re_nba"); };
  sched.ScheduleEvent({0}, Region::kPreReNBA, pre_re_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_re_nba");
  EXPECT_EQ(order[1], "re_nba");
}

// ---------------------------------------------------------------------------
// §4.4.3.7 + Figure 4-1: ReInactive -> PreReNBA -> ReNBA.
// Pre-Re-NBA executes after ReInactive and before Re-NBA.
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBAExecutesAfterReInactiveBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering.
  schedule(Region::kReNBA, "re_nba");
  schedule(Region::kPreReNBA, "pre_re_nba");
  schedule(Region::kReInactive, "re_inactive");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "re_inactive");
  EXPECT_EQ(order[1], "pre_re_nba");
  EXPECT_EQ(order[2], "re_nba");
}

// ---------------------------------------------------------------------------
// §4.4.3.7 Pre-Re-NBA is part of the reactive region set (§4.4.1).
// Its ordinal lies between ReInactive and Re-NBA.
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBAIsWithinReactiveRegionSet) {
  auto pre_re_nba_ord = static_cast<int>(Region::kPreReNBA);
  auto re_inactive_ord = static_cast<int>(Region::kReInactive);
  auto re_nba_ord = static_cast<int>(Region::kReNBA);
  EXPECT_GT(pre_re_nba_ord, re_inactive_ord);
  EXPECT_LT(pre_re_nba_ord, re_nba_ord);
}

// ---------------------------------------------------------------------------
// §4.4.3.7 "PLI callback control point"
// Multiple PLI callbacks coexist in the Pre-Re-NBA region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBARegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreReNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.7 Pre-Re-NBA events across multiple time slots.
// Each time slot has its own Pre-Re-NBA region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBAEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreReNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.7 "read and write values and create events"
// Pre-Re-NBA is read-write. A Pre-Re-NBA callback reads state that Reactive
// set earlier and overwrites it; a later Re-NBA callback sees the Pre-Re-NBA
// modification. This verifies read-write capability in context.
// ---------------------------------------------------------------------------
TEST(SimCh4437, PreReNBAReadWriteInReactiveRegionSetContext) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int reactive_sample = -1;
  int re_nba_sample = -1;

  // Reactive writes value = 10.
  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  // Pre-Re-NBA reads the Reactive-set value and overwrites it to 55.
  auto* pre_re_nba = sched.GetEventPool().Acquire();
  pre_re_nba->callback = [&]() {
    reactive_sample = value;
    value = 55;
  };
  sched.ScheduleEvent({0}, Region::kPreReNBA, pre_re_nba);

  // Re-NBA samples value — should see 55 from Pre-Re-NBA.
  auto* re_nba = sched.GetEventPool().Acquire();
  re_nba->callback = [&]() { re_nba_sample = value; };
  sched.ScheduleEvent({0}, Region::kReNBA, re_nba);

  sched.Run();
  EXPECT_EQ(reactive_sample, 10);
  EXPECT_EQ(re_nba_sample, 55);
}
