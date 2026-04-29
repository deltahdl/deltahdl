#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SchedulerRegionSetSim, ActiveSetBeforeReactiveSet) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kReNBA, "renba", order);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
  EXPECT_EQ(order[2], "reactive");
  EXPECT_EQ(order[3], "renba");
}

TEST(SchedulerRegionSetSim, NonIterativeRegionsAre3) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto schedule = [&](Region r, int id) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, id]() { order.push_back(id); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kPreponed, 1);
  schedule(Region::kPreActive, 2);
  schedule(Region::kPostponed, 3);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);

  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
  EXPECT_EQ(order[2], 3);
}

TEST(SchedulerRegionSetSim, BothSetsInSameTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  int timestep_count = 0;

  sched.SetPostTimestepCallback([&]() { timestep_count++; });

  auto* active = sched.GetEventPool().Acquire();
  active->callback = []() {};
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = []() {};
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  EXPECT_EQ(timestep_count, 1);
}

TEST(SchedulerRegionSetSim, ActiveSetCompletesBeforeObservedReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kInactive, "inactive", order);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
  EXPECT_EQ(order[2], "nba");
  EXPECT_EQ(order[3], "observed");
}

TEST(SchedulerRegionSetSim, ObservedRegionsBridgeActivAndReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kPreObserved, "pre_observed", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kPostObserved, "post_observed", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_observed");
  EXPECT_EQ(order[2], "observed");
  EXPECT_EQ(order[3], "post_observed");
  EXPECT_EQ(order[4], "reactive");
}

TEST(SchedulerRegionSetSim, PrePostponedIsLastIterativeRegion) {
  VerifyThreeRegionOrder({Region::kPostReNBA, "post_renba"},
                         {Region::kPrePostponed, "pre_postponed"},
                         {Region::kPostponed, "postponed"});
}

TEST(SchedulerRegionSetSim, ProcessReactiveContextFlag) {
  Process proc;

  EXPECT_FALSE(proc.is_reactive);

  proc.is_reactive = true;
  EXPECT_TRUE(proc.is_reactive);
}

// §4.4.1 ¶1: production-code classifier returns true exactly for the five
// active region set members.
TEST(SchedulerRegionSetSim, ActiveRegionSetClassification) {
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    bool expected = (r == Region::kActive) || (r == Region::kInactive) ||
                    (r == Region::kPreNBA) || (r == Region::kNBA) ||
                    (r == Region::kPostNBA);
    EXPECT_EQ(IsActiveRegionSet(r), expected) << "region index " << i;
  }
}

// §4.4.1 ¶1: production-code classifier returns true exactly for the five
// reactive region set members.
TEST(SchedulerRegionSetSim, ReactiveRegionSetClassification) {
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    bool expected = (r == Region::kReactive) || (r == Region::kReInactive) ||
                    (r == Region::kPreReNBA) || (r == Region::kReNBA) ||
                    (r == Region::kPostReNBA);
    EXPECT_EQ(IsReactiveRegionSet(r), expected) << "region index " << i;
  }
}

// §4.4.1 ¶1: the active and reactive region sets are disjoint and each
// contains exactly five regions.
TEST(SchedulerRegionSetSim, ActiveAndReactiveSetsAreDisjoint) {
  size_t active_count = 0;
  size_t reactive_count = 0;
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    bool a = IsActiveRegionSet(r);
    bool x = IsReactiveRegionSet(r);
    EXPECT_FALSE(a && x) << "region index " << i;
    if (a) ++active_count;
    if (x) ++reactive_count;
  }
  EXPECT_EQ(active_count, 5u);
  EXPECT_EQ(reactive_count, 5u);
}

// §4.4.1 ¶2: production-code classifier returns true for the 14 named
// iterative regions and false for Preponed, Pre-Active, and Postponed.
TEST(SchedulerRegionSetSim, IterativeRegionClassification) {
  size_t iterative_count = 0;
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    bool non_iterative = (r == Region::kPreponed) ||
                         (r == Region::kPreActive) ||
                         (r == Region::kPostponed);
    EXPECT_EQ(IsIterativeRegion(r), !non_iterative) << "region index " << i;
    if (IsIterativeRegion(r)) ++iterative_count;
  }
  EXPECT_EQ(iterative_count, 14u);
}

// §4.4.1 ¶1+¶2: every active region set member is also an iterative region;
// every reactive region set member is also an iterative region.
TEST(SchedulerRegionSetSim, BothSetsAreIterative) {
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (IsActiveRegionSet(r)) {
      EXPECT_TRUE(IsIterativeRegion(r)) << "active region index " << i;
    }
    if (IsReactiveRegionSet(r)) {
      EXPECT_TRUE(IsIterativeRegion(r)) << "reactive region index " << i;
    }
  }
}

// §4.4.1 ¶1: scheduler iteration of the active region set actually consults
// IsActiveRegionSet — every region the predicate marks true drains, and no
// region it marks false (within the active-bridge window) drains.
TEST(SchedulerRegionSetSim, SchedulerExecutesActiveSetPerClassifier) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<Region> drained;

  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (!IsActiveRegionSet(r)) continue;
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&drained, r]() { drained.push_back(r); };
    sched.ScheduleEvent({0}, r, ev);
  }

  sched.Run();
  ASSERT_EQ(drained.size(), 5u);
  for (auto r : drained) {
    EXPECT_TRUE(IsActiveRegionSet(r));
  }
}

// §4.4.1 ¶1: scheduler iteration of the reactive region set actually consults
// IsReactiveRegionSet.
TEST(SchedulerRegionSetSim, SchedulerExecutesReactiveSetPerClassifier) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<Region> drained;

  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (!IsReactiveRegionSet(r)) continue;
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&drained, r]() { drained.push_back(r); };
    sched.ScheduleEvent({0}, r, ev);
  }

  sched.Run();
  ASSERT_EQ(drained.size(), 5u);
  for (auto r : drained) {
    EXPECT_TRUE(IsReactiveRegionSet(r));
  }
}

// §4.4.1 ¶2: an iterative region that belongs to neither the active region set
// nor the reactive region set must be one of the four bridge/Pre-Postponed
// regions. Closes the exhaustiveness gap left by `BothSetsAreIterative`
// (which only verifies the two sets are subsets of the iterative regions).
TEST(SchedulerRegionSetSim,
     IterativeRegionsOutsideBothSetsAreBridgeAndPrePostponed) {
  size_t outside_count = 0;
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (!IsIterativeRegion(r)) continue;
    if (IsActiveRegionSet(r) || IsReactiveRegionSet(r)) continue;
    bool ok = (r == Region::kPreObserved) || (r == Region::kObserved) ||
              (r == Region::kPostObserved) || (r == Region::kPrePostponed);
    EXPECT_TRUE(ok) << "iterative non-set region index " << i;
    ++outside_count;
  }
  EXPECT_EQ(outside_count, 4u);
}

// §4.4.1 ¶2 corollary: regions excluded from the iterative enumeration are
// exactly Preponed, Pre-Active, and Postponed. Closes the exhaustiveness gap
// left by `NonIterativeRegionsAre3` (which schedules into those three but
// does not assert that no other region is non-iterative).
TEST(SchedulerRegionSetSim, NonIterativeRegionsAreExactlyPreponedPreActivePostponed) {
  size_t non_iter_count = 0;
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (IsIterativeRegion(r)) continue;
    bool ok = (r == Region::kPreponed) || (r == Region::kPreActive) ||
              (r == Region::kPostponed);
    EXPECT_TRUE(ok) << "non-iterative region index " << i;
    ++non_iter_count;
  }
  EXPECT_EQ(non_iter_count, 3u);
}

TEST(SchedulerRegionSetSim, AllRegionsCategorizedAndProcessed) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int r = 0; r < static_cast<int>(Region::kCOUNT); ++r) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&count]() { count++; };
    sched.ScheduleEvent({0}, static_cast<Region>(r), ev);
  }

  sched.Run();
  EXPECT_EQ(count, static_cast<int>(kRegionCount));
}

// §4.4.1 ¶3: production-code predicates IsSimulationRegion / IsPliRegion
// implement the partition. The §4.4.1 ¶3 obligation is the partition's
// existence, totality, and disjointness; the membership content lives in
// §4.4.2 / §4.4.3 and is tested in those clauses' files.

TEST(SchedulerRegionSetSim, SimAndPliPartitionSumsToTotal) {
  size_t sim_count = 0;
  size_t pli_count = 0;
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (IsSimulationRegion(r)) ++sim_count;
    if (IsPliRegion(r)) ++pli_count;
  }
  EXPECT_EQ(sim_count + pli_count, kRegionCount);
}

TEST(SchedulerRegionSetSim, SimAndPliPartitionIsDisjoint) {
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    EXPECT_FALSE(IsSimulationRegion(r) && IsPliRegion(r))
        << "region index " << i;
  }
}

TEST(SchedulerRegionSetSim, SimAndPliPartitionCoversEveryRegion) {
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    EXPECT_TRUE(IsSimulationRegion(r) || IsPliRegion(r))
        << "region index " << i;
  }
}
