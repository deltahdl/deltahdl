#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.1 Active region sets and reactive region sets
//
// LRM §4.4.1 defines two important groupings of event regions:
//
//   Active region set:
//     Active, Inactive, Pre-NBA, NBA, Post-NBA
//
//   Reactive region set:
//     Reactive, Re-Inactive, Pre-Re-NBA, Re-NBA, Post-Re-NBA
//
//   Iterative regions (14 total):
//     Active, Inactive, Pre-NBA, NBA, Post-NBA,
//     Pre-Observed, Observed, Post-Observed,
//     Reactive, Re-Inactive, Pre-Re-NBA, Re-NBA, Post-Re-NBA,
//     Pre-Postponed
//
//   The remaining 3 regions (Preponed, Pre-Active, Postponed) are
//   NOT iterative.
//
//   In addition, all regions can be categorized as simulation regions
//   (see 4.4.2) or PLI regions (see 4.4.3).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.1 Active region set membership: Active, Inactive, Pre-NBA, NBA,
// Post-NBA.  These five regions form the active region set and are iterated
// together by the scheduler.
// ---------------------------------------------------------------------------
TEST(SimCh441, ActiveRegionSetMembership) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // Schedule one event in each active-set region.
  auto schedule = [&](Region r, int id) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, id]() { order.push_back(id); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kActive, 1);
  schedule(Region::kInactive, 2);
  schedule(Region::kPreNBA, 3);
  schedule(Region::kNBA, 4);
  schedule(Region::kPostNBA, 5);

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
  EXPECT_EQ(order[2], 3);
  EXPECT_EQ(order[3], 4);
  EXPECT_EQ(order[4], 5);
}

// ---------------------------------------------------------------------------
// §4.4.1 Reactive region set membership: Reactive, Re-Inactive,
// Pre-Re-NBA, Re-NBA, Post-Re-NBA.  These five regions form the reactive
// region set and are iterated together.
// ---------------------------------------------------------------------------
TEST(SimCh441, ReactiveRegionSetMembership) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto schedule = [&](Region r, int id) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, id]() { order.push_back(id); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kReactive, 1);
  schedule(Region::kReInactive, 2);
  schedule(Region::kPreReNBA, 3);
  schedule(Region::kReNBA, 4);
  schedule(Region::kPostReNBA, 5);

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
  EXPECT_EQ(order[2], 3);
  EXPECT_EQ(order[3], 4);
  EXPECT_EQ(order[4], 5);
}

// ---------------------------------------------------------------------------
// §4.4.1 Active region set events execute before reactive region set events
// within the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh441, ActiveSetBeforeReactiveSet) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule reactive first, active second — active should still run first.
  schedule(Region::kReactive, "reactive");
  schedule(Region::kActive, "active");
  schedule(Region::kNBA, "nba");
  schedule(Region::kReNBA, "renba");

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
  EXPECT_EQ(order[2], "reactive");
  EXPECT_EQ(order[3], "renba");
}

// ---------------------------------------------------------------------------
// §4.4.1 Iterative regions: 14 regions that participate in the iterative
// loop.  This test enumerates all 14 iterative regions and verifies they
// all execute.
// ---------------------------------------------------------------------------
TEST(SimCh441, IterativeRegionsAre14) {
  Arena arena;
  Scheduler sched(arena);

  // The 14 iterative regions per §4.4.1.
  const Region kIterative[] = {
      Region::kActive,     Region::kInactive,     Region::kPreNBA,
      Region::kNBA,        Region::kPostNBA,      Region::kPreObserved,
      Region::kObserved,   Region::kPostObserved, Region::kReactive,
      Region::kReInactive, Region::kPreReNBA,     Region::kReNBA,
      Region::kPostReNBA,  Region::kPrePostponed,
  };

  int count = 0;
  for (auto r : kIterative) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&count]() { count++; };
    sched.ScheduleEvent({0}, r, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 14);
}

// ---------------------------------------------------------------------------
// §4.4.1 Non-iterative regions: Preponed, Pre-Active, and Postponed are
// the 3 regions that are NOT iterative.  They still execute, but outside
// the iterative loop.
// ---------------------------------------------------------------------------
TEST(SimCh441, NonIterativeRegionsAre3) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // The 3 non-iterative regions.
  auto schedule = [&](Region r, int id) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, id]() { order.push_back(id); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kPreponed, 1);
  schedule(Region::kPreActive, 2);
  schedule(Region::kPostponed, 3);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  // They execute in region order: Preponed < Pre-Active < Postponed.
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
  EXPECT_EQ(order[2], 3);
}

// ---------------------------------------------------------------------------
// §4.4.1 All 17 regions = 14 iterative + 3 non-iterative.
// Verify this partitioning is exhaustive.
// ---------------------------------------------------------------------------
TEST(SimCh441, IterativePlusNonIterativeEquals17) {
  constexpr size_t kIterativeCount = 14;
  constexpr size_t kNonIterativeCount = 3;
  EXPECT_EQ(kIterativeCount + kNonIterativeCount, kRegionCount);
}

// ---------------------------------------------------------------------------
// §4.4.1 Active region set iteration: events scheduled within the active
// set during execution (feedback) cause re-iteration until stable.
// An Active callback that schedules an NBA event triggers re-draining.
// ---------------------------------------------------------------------------
TEST(SimCh441, ActiveSetFeedbackReiterates) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    order.push_back("active");
    // Scheduling an NBA event within the active set iteration.
    auto *nba = sched.GetEventPool().Acquire();
    nba->callback = [&order]() { order.push_back("nba"); };
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
}

// ---------------------------------------------------------------------------
// §4.4.1 Reactive region set iteration: events within the reactive set
// cause re-iteration.  A Reactive callback that schedules a Re-NBA event
// triggers re-draining of the reactive set.
// ---------------------------------------------------------------------------
TEST(SimCh441, ReactiveSetFeedbackReiterates) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    order.push_back("reactive");
    auto *renba = sched.GetEventPool().Acquire();
    renba->callback = [&order]() { order.push_back("renba"); };
    sched.ScheduleEvent({0}, Region::kReNBA, renba);
  };
  sched.ScheduleEvent({0}, Region::kReactive, ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "renba");
}

// ---------------------------------------------------------------------------
// §4.4.1 Reactive-to-active restart: a reactive region event that schedules
// an active region event causes the scheduler to restart the active set
// iteration.
// ---------------------------------------------------------------------------
TEST(SimCh441, ReactiveRestartsActiveSetIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // First: normal active event.
  auto *first = sched.GetEventPool().Acquire();
  first->callback = [&order]() { order.push_back("active1"); };
  sched.ScheduleEvent({0}, Region::kActive, first);

  // Reactive event schedules a new Active event.
  auto *reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    auto *active2 = sched.GetEventPool().Acquire();
    active2->callback = [&order]() { order.push_back("active2"); };
    sched.ScheduleEvent({0}, Region::kActive, active2);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active1");
  EXPECT_EQ(order[1], "reactive");
  EXPECT_EQ(order[2], "active2");
}

// ---------------------------------------------------------------------------
// §4.4.1 Active set and reactive set execute in the same time slot.
// Both groupings are part of the same time step, not separate time steps.
// ---------------------------------------------------------------------------
TEST(SimCh441, BothSetsInSameTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  int timestep_count = 0;

  sched.SetPostTimestepCallback([&]() { timestep_count++; });

  auto *active = sched.GetEventPool().Acquire();
  active->callback = []() {};
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto *reactive = sched.GetEventPool().Acquire();
  reactive->callback = []() {};
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  EXPECT_EQ(timestep_count, 1);
}

// ---------------------------------------------------------------------------
// §4.4.1 Active region set fully iterates before the Observed/Reactive
// regions begin.
// ---------------------------------------------------------------------------
TEST(SimCh441, ActiveSetCompletesBeforeObservedReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kObserved, "observed");
  schedule(Region::kActive, "active");
  schedule(Region::kNBA, "nba");
  schedule(Region::kInactive, "inactive");

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
  EXPECT_EQ(order[2], "nba");
  EXPECT_EQ(order[3], "observed");
}

// ---------------------------------------------------------------------------
// §4.4.1 Iterative regions: Pre-Observed, Observed, Post-Observed bridge
// the active and reactive sets.  They execute after the active set is
// stable and before the reactive set regions.
// ---------------------------------------------------------------------------
TEST(SimCh441, ObservedRegionsBridgeActivAndReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kActive, "active");
  schedule(Region::kPreObserved, "pre_observed");
  schedule(Region::kObserved, "observed");
  schedule(Region::kPostObserved, "post_observed");
  schedule(Region::kReactive, "reactive");

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_observed");
  EXPECT_EQ(order[2], "observed");
  EXPECT_EQ(order[3], "post_observed");
  EXPECT_EQ(order[4], "reactive");
}

// ---------------------------------------------------------------------------
// §4.4.1 Pre-Postponed is the last iterative region.  It executes after
// all reactive regions and before the non-iterative Postponed region.
// ---------------------------------------------------------------------------
TEST(SimCh441, PrePostponedIsLastIterativeRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kPostReNBA, "post_renba");
  schedule(Region::kPrePostponed, "pre_postponed");
  schedule(Region::kPostponed, "postponed");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "post_renba");
  EXPECT_EQ(order[1], "pre_postponed");
  EXPECT_EQ(order[2], "postponed");
}

// ---------------------------------------------------------------------------
// §4.4.1 "In addition to the active region set and reactive region set,
// all of the event regions of each time slot can be categorized as
// simulation regions (see 4.4.2) or PLI regions (see 4.4.3)."
//
// This cross-reference implies a dual categorization of regions.  The
// scheduler processes all 17 regions regardless of category, and each
// region belongs to exactly one category.  Test that all 17 regions
// are processed.
// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// §4.4.1 Process reactive context: the is_reactive flag distinguishes
// processes in the active region set from those in the reactive region set.
// ---------------------------------------------------------------------------
TEST(SimCh441, ProcessReactiveContextFlag) {
  Process proc;
  // Default should be non-reactive (active context).
  EXPECT_FALSE(proc.is_reactive);

  // Setting to reactive context.
  proc.is_reactive = true;
  EXPECT_TRUE(proc.is_reactive);
}

// ---------------------------------------------------------------------------
// §4.4.1 All 17 regions = simulation regions + PLI regions.  The scheduler
// processes all of them regardless of category.
// ---------------------------------------------------------------------------
TEST(SimCh441, AllRegionsCategorizedAndProcessed) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int r = 0; r < static_cast<int>(Region::kCOUNT); ++r) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&count]() { count++; };
    sched.ScheduleEvent({0}, static_cast<Region>(r), ev);
  }

  sched.Run();
  EXPECT_EQ(count, static_cast<int>(kRegionCount));
}
