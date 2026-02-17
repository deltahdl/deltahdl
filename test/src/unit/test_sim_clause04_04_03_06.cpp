#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.6 Post-Observed PLI region
//
// LRM §4.4.3.6:
//   "The Post-Observed region provides for a PLI callback control point that
//    allows PLI application routines to read values after properties are
//    evaluated (in the Observed or an earlier region)."
//
//   "NOTE—The PLI currently does not schedule callbacks in the
//    Post-Observed region."
//
// Figure 4-1 shows:
//   region_Observed -> pli_region_PostObserved -> region_Reactive
//
// The Post-Observed region is a read-only PLI callback control point.
// Post-Observed is part of the reactive region set (§4.4.1 iterative regions).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.6 "provides for a PLI callback control point"
// Basic: events scheduled in the Post-Observed region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPostObserved, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.6 "allows PLI application routines to read values"
// A Post-Observed callback can read state set by the active region set.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Active sets value = 42.
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Post-Observed reads value — should see 42.
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostObserved, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.6 "after properties are evaluated (in the Observed or an earlier
// region)"
// Post-Observed sees state set by the Observed region.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedReadsAfterObservedRegion) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Observed sets value = 77 (simulating property evaluation side-effect).
  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { value = 77; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  // Post-Observed should see 77.
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostObserved, ev);

  sched.Run();
  EXPECT_EQ(sampled, 77);
}

// ---------------------------------------------------------------------------
// §4.4.3.6 + Figure 4-1: Observed -> PostObserved -> Reactive.
// Post-Observed executes after Observed and before Reactive.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedExecutesAfterObservedBeforeReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering.
  schedule(Region::kReactive, "reactive");
  schedule(Region::kPostObserved, "post_observed");
  schedule(Region::kObserved, "observed");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "post_observed");
  EXPECT_EQ(order[2], "reactive");
}

// ---------------------------------------------------------------------------
// §4.4.3.6 "after properties are evaluated (in the Observed or an earlier
// region)"
// Post-Observed sees state from the entire chain: Active set -> Observed.
// Full chain: Active -> NBA -> PostNBA -> PreObserved -> Observed ->
// PostObserved.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedExecutesAfterEntireChainThroughObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse to prove region ordering, not insertion order.
  schedule(Region::kPostObserved, "post_observed");
  schedule(Region::kObserved, "observed");
  schedule(Region::kPreObserved, "pre_observed");
  schedule(Region::kActive, "active");

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_observed");
  EXPECT_EQ(order[2], "observed");
  EXPECT_EQ(order[3], "post_observed");
}

// ---------------------------------------------------------------------------
// §4.4.3.6 Post-Observed ordinal lies between Observed and Reactive.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedIsAfterObservedBeforeReactive) {
  auto post_observed_ord = static_cast<int>(Region::kPostObserved);
  auto observed_ord = static_cast<int>(Region::kObserved);
  auto reactive_ord = static_cast<int>(Region::kReactive);
  EXPECT_GT(post_observed_ord, observed_ord);
  EXPECT_LT(post_observed_ord, reactive_ord);
}

// ---------------------------------------------------------------------------
// §4.4.3.6 "PLI callback control point"
// Multiple PLI callbacks coexist in the Post-Observed region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostObserved, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.6 Post-Observed events across multiple time slots.
// Each time slot has its own Post-Observed region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPostObserved, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.6 "read values after properties are evaluated"
// Post-Observed is read-only. This test confirms that Post-Observed executes
// after Observed, so a PLI callback sampling state sees the snapshot produced
// by property evaluation in the Observed region.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedProvidesReadOnlySnapshotAfterObserved) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int sum_in_post_observed = -1;

  // Active sets initial values, Observed modifies them (property evaluation).
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    a = 10;
    b = 20;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { b = 30; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  // Post-Observed reads both — should see a=10, b=30 (Observed overwrote b).
  auto* post_obs = sched.GetEventPool().Acquire();
  post_obs->callback = [&]() { sum_in_post_observed = a + b; };
  sched.ScheduleEvent({0}, Region::kPostObserved, post_obs);

  sched.Run();
  EXPECT_EQ(sum_in_post_observed, 40);
}

// ---------------------------------------------------------------------------
// §4.4.3.6 "NOTE—The PLI currently does not schedule callbacks in the
// Post-Observed region."
// Even though no PLI currently uses this region, the infrastructure must
// still correctly process events placed here. This test schedules a
// Post-Observed event alongside a full set of surrounding regions and
// verifies the complete ordering is respected.
// ---------------------------------------------------------------------------
TEST(SimCh4436, PostObservedInfrastructureWorksEvenIfCurrentlyUnused) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kReactive, "reactive");
  schedule(Region::kPostObserved, "post_observed");
  schedule(Region::kObserved, "observed");
  schedule(Region::kPreObserved, "pre_observed");
  schedule(Region::kPostNBA, "post_nba");
  schedule(Region::kActive, "active");

  sched.Run();
  ASSERT_EQ(order.size(), 6u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "post_nba");
  EXPECT_EQ(order[2], "pre_observed");
  EXPECT_EQ(order[3], "observed");
  EXPECT_EQ(order[4], "post_observed");
  EXPECT_EQ(order[5], "reactive");
}
