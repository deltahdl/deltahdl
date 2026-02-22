#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.1 Preponed PLI region
//
// Figure 4-1 shows:
//   region_Preponed -> pli_region_PreActive  (first region in time slot)
//
// The Preponed region is the very first region executed in each time slot.
// It is a read-only observation point for PLI callbacks.
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.1 Preponed PLI callback control point
// Basic: events scheduled in the Preponed region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPreponed, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.1 Read-only access before state changes
// Preponed executes before Active, so it sees state from the previous time
// slot (or initial state).
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedAccessesDataBeforeAnyStateChange) {
  Arena arena;
  Scheduler sched(arena);
  int value = 42;
  int sampled_in_preponed = -1;

  // Active at time 0 changes value.
  auto *active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 100; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Preponed at time 0 samples value — should see original (42).
  auto *preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled_in_preponed = value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sampled_in_preponed, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.1 Preponed sees pre-change state
// Preponed sees the state BEFORE all simulation regions (Active, Inactive,
// NBA, Observed, Reactive, Re-Inactive, Re-NBA) modify it.
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedSeesStateBeforeAllSimulationRegions) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Multiple simulation regions all modify value.
  auto schedule_mod = [&](Region r, int new_val) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&value, new_val]() { value = new_val; };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule_mod(Region::kActive, 10);
  schedule_mod(Region::kInactive, 20);
  schedule_mod(Region::kNBA, 30);
  schedule_mod(Region::kReactive, 40);
  schedule_mod(Region::kReNBA, 50);

  // Preponed should see value = 0 (initial state).
  auto *preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sampled, 0);
}

// ---------------------------------------------------------------------------
// §4.4.3.1 + Figure 4-1: region_Preponed -> pli_region_PreActive
// Preponed is the very first region in a time slot, executing before
// PreActive and all subsequent regions.
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedExecutesBeforePreActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto *pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { order.push_back("pre_active"); };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  auto *preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { order.push_back("preponed"); };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "preponed");
  EXPECT_EQ(order[1], "pre_active");
}

// ---------------------------------------------------------------------------
// §4.4.3.1 Preponed is the first region — ordinal 0 in the Region enum.
// This confirms its position as the very first region per §4.4 ordering.
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedIsFirstRegionOrdinal) {
  EXPECT_EQ(static_cast<int>(Region::kPreponed), 0);
}

// ---------------------------------------------------------------------------
// §4.4.3.1 Multiple Preponed callbacks
// Multiple PLI callbacks coexist in the Preponed region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.1 Preponed data access across time slots
// Preponed at time T sees state left by Postponed at time T-1 (the final
// state of the previous time slot).
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedSeesStatefromPreviousTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_t1 = -1;

  // Active at time 0 sets value = 77.
  auto *active0 = sched.GetEventPool().Acquire();
  active0->callback = [&]() { value = 77; };
  sched.ScheduleEvent({0}, Region::kActive, active0);

  // Preponed at time 1 should see value = 77 (final state from time 0).
  auto *preponed1 = sched.GetEventPool().Acquire();
  preponed1->callback = [&]() { sampled_t1 = value; };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed1);

  sched.Run();
  EXPECT_EQ(sampled_t1, 77);
}

// ---------------------------------------------------------------------------
// §4.4.3.1 Preponed executes before ALL other regions in the same time slot.
// Full ordering: Preponed < PreActive < Active < ... < Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedExecutesBeforeAllOtherRegions) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering, not insertion order.
  schedule(Region::kPostponed, "postponed");
  schedule(Region::kActive, "active");
  schedule(Region::kNBA, "nba");
  schedule(Region::kReactive, "reactive");
  schedule(Region::kPreponed, "preponed");

  sched.Run();
  ASSERT_GE(order.size(), 5u);
  EXPECT_EQ(order[0], "preponed");
}

// ---------------------------------------------------------------------------
// §4.4.3.1 Preponed events across multiple time slots.
// Each time slot has its own Preponed region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreponed, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.1 Preponed is read-only
// The Preponed region is read-only. This test confirms that Preponed
// executes in isolation before any state-modifying region, so a PLI
// callback sampling state sees a consistent snapshot.
// ---------------------------------------------------------------------------
TEST(SimCh4431, PreponedProvidesConsistentReadOnlySnapshot) {
  Arena arena;
  Scheduler sched(arena);
  int a = 1;
  int b = 2;
  int sum_in_preponed = -1;

  // Active at time 0 will change both a and b.
  auto *active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    a = 100;
    b = 200;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Preponed at time 0 reads both — should see original values.
  auto *preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sum_in_preponed = a + b; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sum_in_preponed, 3);
}
