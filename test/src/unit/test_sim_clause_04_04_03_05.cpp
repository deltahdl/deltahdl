#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.5 Pre-Observed PLI region
//
// LRM §4.4.3.5:
//   "The Pre-Observed region provides for a PLI callback control point that
//    allows PLI application routines to read values after the active region
//    set has stabilized. Within this region, it is illegal to write values
//    to any net or variable or to schedule an event within the current time
//    slot."
//
// Figure 4-1 shows:
//   pli_region_PostNBA -> pli_region_PreObserved -> region_Observed
//
// The Pre-Observed region is a read-only PLI callback control point.
// Pre-Observed is part of the reactive region set (§4.4.1 iterative regions).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.5 "provides for a PLI callback control point"
// Basic: events scheduled in the Pre-Observed region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPreObserved, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.5 "allows PLI application routines to read values"
// A Pre-Observed callback can read state set by the active region set.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Active sets value = 42.
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Pre-Observed reads value — should see 42.
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreObserved, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.5 "read values after the active region set has stabilized"
// Pre-Observed sees final state from the entire active region set
// (PreActive, Active, Inactive, PreNBA, NBA, PostNBA), not just Active.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedReadsAfterActiveRegionSetStabilized) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // PostNBA is the last region in the active region set.
  // It overwrites what Active set.
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() { value = 77; };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  // Pre-Observed should see 77 (final state after active set stabilized).
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreObserved, ev);

  sched.Run();
  EXPECT_EQ(sampled, 77);
}

// ---------------------------------------------------------------------------
// §4.4.3.5 + Figure 4-1: PostNBA -> PreObserved -> Observed.
// Pre-Observed executes after PostNBA and before Observed.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedExecutesAfterPostNBABeforeObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering.
  schedule(Region::kObserved, "observed");
  schedule(Region::kPreObserved, "pre_observed");
  schedule(Region::kPostNBA, "post_nba");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "post_nba");
  EXPECT_EQ(order[1], "pre_observed");
  EXPECT_EQ(order[2], "observed");
}

// ---------------------------------------------------------------------------
// §4.4.3.5 "after the active region set has stabilized"
// Pre-Observed executes after the entire active region set, not just Active.
// Full chain: Active -> Inactive -> PreNBA -> NBA -> PostNBA -> PreObserved.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedExecutesAfterEntireActiveRegionSet) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse to prove region ordering, not insertion order.
  schedule(Region::kPreObserved, "pre_observed");
  schedule(Region::kPostNBA, "post_nba");
  schedule(Region::kNBA, "nba");
  schedule(Region::kActive, "active");

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
  EXPECT_EQ(order[2], "post_nba");
  EXPECT_EQ(order[3], "pre_observed");
}

// ---------------------------------------------------------------------------
// §4.4.3.5 Pre-Observed ordinal lies between PostNBA and Observed.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedIsAfterPostNBABeforeObserved) {
  auto pre_observed_ord = static_cast<int>(Region::kPreObserved);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  auto observed_ord = static_cast<int>(Region::kObserved);
  EXPECT_GT(pre_observed_ord, post_nba_ord);
  EXPECT_LT(pre_observed_ord, observed_ord);
}

// ---------------------------------------------------------------------------
// §4.4.3.5 "PLI callback control point"
// Multiple PLI callbacks coexist in the Pre-Observed region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreObserved, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.5 Pre-Observed events across multiple time slots.
// Each time slot has its own Pre-Observed region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreObserved, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.5 "it is illegal to write values to any net or variable"
// Pre-Observed is read-only. This test confirms that Pre-Observed executes
// in isolation after the active set, so a PLI callback sampling state sees
// the stable snapshot produced by the active region set.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedProvidesReadOnlySnapshotAfterActiveSet) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int sum_in_pre_observed = -1;

  // Active at time 0 sets both a and b.
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    a = 10;
    b = 20;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Pre-Observed reads both — should see the values Active set.
  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() { sum_in_pre_observed = a + b; };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  EXPECT_EQ(sum_in_pre_observed, 30);
}

// ---------------------------------------------------------------------------
// §4.4.3.5 "read values after the active region set has stabilized"
// Pre-Observed reads the fully-stabilized state, even when multiple active
// region set iterations occur due to feedback (Active -> Inactive -> Active).
// The final value after all active-set iterations is what Pre-Observed sees.
// ---------------------------------------------------------------------------
TEST(SimCh4435, PreObservedReadsFullyStabilizedActiveSetState) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Active sets value = 1, then schedules an Inactive event that
  // re-enters Active with value = 99. After active set stabilizes,
  // Pre-Observed should see 99.
  auto set_final = [&]() { value = 99; };
  auto schedule_reentry = [&]() {
    auto* active2 = sched.GetEventPool().Acquire();
    active2->callback = set_final;
    sched.ScheduleEvent({0}, Region::kActive, active2);
  };

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    if (value == 0) {
      value = 1;
      auto* inactive = sched.GetEventPool().Acquire();
      inactive->callback = schedule_reentry;
      sched.ScheduleEvent({0}, Region::kInactive, inactive);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Pre-Observed samples the fully-stabilized value.
  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  EXPECT_EQ(sampled, 99);
}
