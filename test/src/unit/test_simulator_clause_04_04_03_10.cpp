#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.10 Postponed PLI region
//
// Figure 4-1 shows:
//   pli_region_PrePostponed -> region_Postponed
//
// The Postponed region is a read-only PLI callback control point.
// Postponed is the last region in the time slot.
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.10 Postponed PLI callback control point
// Basic: events scheduled in the Postponed region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPostponed, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.10 Postponed read-only event creation
// A Postponed callback can read state set by all preceding regions.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Pre-Postponed sets value = 42.
  auto *pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  // Postponed reads value — should see 42.
  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.10 Postponed reads cumulative state
// Postponed sees the cumulative state from the entire active + reactive chain.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedReadsStateFromActiveAndReactiveRegions) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Active sets value = 10.
  auto *active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Reactive overwrites value = 77.
  auto *reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { value = 77; };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  // Postponed reads — should see 77 (the final state after all regions).
  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, ev);

  sched.Run();
  EXPECT_EQ(sampled, 77);
}

// ---------------------------------------------------------------------------
// §4.4.3.10 Postponed executes after all other regions
// Postponed executes after Pre-Postponed in the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedExecutesAfterPrePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule Postponed first, then Pre-Postponed — ordering must still hold.
  auto *postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { order.push_back("postponed"); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  auto *pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { order.push_back("pre_postponed"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_postponed");
  EXPECT_EQ(order[1], "postponed");
}

// ---------------------------------------------------------------------------
// §4.4.3.10 + Figure 4-1: PrePostponed -> Postponed (final region).
// Postponed executes after every other region in the time slot.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedIsLastRegionInTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering.
  schedule(Region::kPostponed, "postponed");
  schedule(Region::kPrePostponed, "pre_postponed");
  schedule(Region::kReactive, "reactive");
  schedule(Region::kActive, "active");
  schedule(Region::kPreponed, "preponed");

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  EXPECT_EQ(order[0], "preponed");
  EXPECT_EQ(order[1], "active");
  EXPECT_EQ(order[2], "reactive");
  EXPECT_EQ(order[3], "pre_postponed");
  EXPECT_EQ(order[4], "postponed");
}

// ---------------------------------------------------------------------------
// §4.4.3.10 Postponed is the last region in the enum (before kCOUNT).
// Its ordinal is greater than every other region.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedIsLastRegionOrdinal) {
  auto postponed_ord = static_cast<int>(Region::kPostponed);
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  auto count_ord = static_cast<int>(Region::kCOUNT);
  EXPECT_GT(postponed_ord, pre_postponed_ord);
  EXPECT_EQ(postponed_ord, count_ord - 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.10 Multiple Postponed callbacks
// Multiple PLI callbacks coexist in the Postponed region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.10 Postponed events across multiple time slots.
// Each time slot has its own Postponed region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPostponed, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.10 Postponed provides read-only snapshot
// Postponed is read-only. A Postponed callback reads the final state produced
// by the full region chain (Preponed through Pre-Postponed). This verifies
// that Postponed provides a consistent snapshot of completed simulation state.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedProvidesReadOnlySnapshotAfterAllRegions) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int sum_in_postponed = -1;

  // Active sets initial values.
  auto *active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    a = 10;
    b = 20;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Pre-Postponed modifies b (last read-write region before Postponed).
  auto *pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { b = 30; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  // Postponed reads both — should see a=10, b=30 (Pre-Postponed overwrote b).
  auto *postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sum_in_postponed = a + b; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sum_in_postponed, 40);
}

// ---------------------------------------------------------------------------
// §4.4.3.10 Postponed infrastructure with full region chain
// Postponed region correctly processes all events in the time slot, including
// alongside a full set of surrounding regions from all region sets.
// ---------------------------------------------------------------------------
TEST(SimCh44310, PostponedInfrastructureWithFullRegionChain) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kPostponed, "postponed");
  schedule(Region::kPrePostponed, "pre_postponed");
  schedule(Region::kPostReNBA, "post_re_nba");
  schedule(Region::kReactive, "reactive");
  schedule(Region::kPostObserved, "post_observed");
  schedule(Region::kObserved, "observed");
  schedule(Region::kPostNBA, "post_nba");
  schedule(Region::kActive, "active");
  schedule(Region::kPreponed, "preponed");

  sched.Run();
  std::vector<std::string> expected = {
      "preponed", "active",      "post_nba",      "observed", "post_observed",
      "reactive", "post_re_nba", "pre_postponed", "postponed"};
  EXPECT_EQ(order, expected);
}
