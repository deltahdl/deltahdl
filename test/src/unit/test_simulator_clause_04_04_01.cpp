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

// §4.4.1 ¶2: scheduler iteration of the iterative regions actually consults
// IsIterativeRegion — every region the predicate marks true drains, and the
// scheduler's iterative loop processes exactly the 14-region set.
TEST(SchedulerRegionSetSim, SchedulerIteratesIterativeRegionsPerClassifier) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<Region> drained;

  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (!IsIterativeRegion(r)) continue;
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&drained, r]() { drained.push_back(r); };
    sched.ScheduleEvent({0}, r, ev);
  }

  sched.Run();
  ASSERT_EQ(drained.size(), 14u);
  for (auto r : drained) {
    EXPECT_TRUE(IsIterativeRegion(r));
  }
}

// §4.4.1 ¶2 edge cases for the iterative-loop gate. Direct test of the
// production-code path TimeSlot::AnyIterativeNonempty (which routes through
// IsIterativeRegion) covers three states that end-to-end scheduler tests
// either can't reach or would manifest as an infinite loop rather than a
// clean failure: an empty slot, a slot whose only events are in non-iterative
// regions (the §4.4.1 ¶2 exclusion set: Preponed, Pre-Active, Postponed), and
// a slot with a single event in an iterative region. A predicate that
// misclassified Postponed as iterative would hang ExecuteTimeSlot; one that
// misclassified Preponed or Pre-Active would go undetected because those
// regions are pre-drained before the loop entry.
TEST(SchedulerRegionSetSim, TimeSlotAnyIterativeNonemptyExcludesNonIterative) {
  Arena arena;
  EventPool pool(arena);
  TimeSlot slot;

  EXPECT_FALSE(slot.AnyIterativeNonempty());

  for (auto r : {Region::kPreponed, Region::kPreActive, Region::kPostponed}) {
    auto* ev = pool.Acquire();
    ev->callback = []() {};
    slot.regions[static_cast<size_t>(r)].Push(ev);
  }
  EXPECT_FALSE(slot.AnyIterativeNonempty());

  auto* ev = pool.Acquire();
  ev->callback = []() {};
  slot.regions[static_cast<size_t>(Region::kPrePostponed)].Push(ev);
  EXPECT_TRUE(slot.AnyIterativeNonempty());
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
