#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.2 Pre-Active PLI region
//
// Figure 4-1 shows:
//   region_Preponed -> pli_region_PreActive -> region_Active
//
// The Pre-Active region is a read-write PLI callback control point.
// Unlike the Preponed region (read-only), Pre-Active allows PLI routines
// to modify state and create new events.
// Pre-Active is part of the active region set (§4.4.1).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.2 Pre-Active PLI callback control point
// Basic: events scheduled in the Pre-Active region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPreActive, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.2 Pre-Active can read values
// A Pre-Active callback can read state set during initialization.
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 42;
  int sampled = -1;

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreActive, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.2 Pre-Active can write values
// A Pre-Active callback can modify state that Active will later observe.
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveCanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_active = -1;

  // Pre-Active writes a value.
  auto *pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  // Active reads the value — should see 99.
  auto *active = sched.GetEventPool().Acquire();
  active->callback = [&]() { sampled_in_active = value; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(sampled_in_active, 99);
}

// ---------------------------------------------------------------------------
// §4.4.3.2 Pre-Active can create events
// A Pre-Active callback can schedule new events (e.g., into Active).
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveCanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto *pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() {
    order.push_back("pre_active");
    // Create an event in the Active region from Pre-Active.
    auto *new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_active"); };
    sched.ScheduleEvent({0}, Region::kActive, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active");
  EXPECT_EQ(order[1], "created_active");
}

// ---------------------------------------------------------------------------
// §4.4.3.2 Pre-Active executes before Active
// Pre-Active executes before Active in the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveExecutesBeforeActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule Active first, then Pre-Active — ordering must still hold.
  auto *active = sched.GetEventPool().Acquire();
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto *pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { order.push_back("pre_active"); };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active");
  EXPECT_EQ(order[1], "active");
}

// ---------------------------------------------------------------------------
// §4.4.3.2 + Figure 4-1: Preponed -> Pre-Active -> Active.
// Pre-Active executes after Preponed and before Active.
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveExecutesAfterPreponedBeforeActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering.
  schedule(Region::kActive, "active");
  schedule(Region::kPreActive, "pre_active");
  schedule(Region::kPreponed, "preponed");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "preponed");
  EXPECT_EQ(order[1], "pre_active");
  EXPECT_EQ(order[2], "active");
}

// ---------------------------------------------------------------------------
// §4.4.3.2 Pre-Active is part of the active region set (§4.4.1).
// Its ordinal lies between Preponed and Active.
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveIsWithinActiveRegionSet) {
  auto pre_active_ord = static_cast<int>(Region::kPreActive);
  auto preponed_ord = static_cast<int>(Region::kPreponed);
  auto active_ord = static_cast<int>(Region::kActive);
  EXPECT_GT(pre_active_ord, preponed_ord);
  EXPECT_LT(pre_active_ord, active_ord);
}

// ---------------------------------------------------------------------------
// §4.4.3.2 Multiple Pre-Active callbacks
// Multiple PLI callbacks coexist in the Pre-Active region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreActive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.2 Pre-Active events across multiple time slots.
// Each time slot has its own Pre-Active region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.2 Pre-Active read-write vs Preponed read-only
// Contrast with §4.4.3.1: Pre-Active is read-write, whereas Preponed is
// read-only. A Pre-Active callback writes state that is visible to a
// later Active callback in the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4432, PreActiveReadWriteContrastWithPreponed) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int preponed_sample = -1;
  int active_sample = -1;

  // Pre-Active writes value = 55.
  auto *pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { value = 55; };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  // Preponed samples value — should see original (0) since it runs first.
  auto *preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { preponed_sample = value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  // Active samples value — should see 55 from Pre-Active.
  auto *active = sched.GetEventPool().Acquire();
  active->callback = [&]() { active_sample = value; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(preponed_sample, 0);
  EXPECT_EQ(active_sample, 55);
}
