#include <gtest/gtest.h>

#include <set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

// §4.4.1 ¶1: "Events scheduled in the Active, Inactive, Pre-NBA, NBA, and
// Post-NBA regions are active region set events." Production code expresses
// the membership rule through IsActiveRegionSet, which the scheduler reads
// when draining the active region set. Walking all 17 regions and asserting
// the predicate returns true for exactly those five — and false for the
// remaining twelve — ties the rule directly to the predicate that production
// code applies.
TEST(ActiveRegionSetSim,
     ActiveRegionSetPredicateAcceptsExactlyTheFiveListedRegions) {
  const std::set<Region> kListed = {Region::kActive, Region::kInactive,
                                    Region::kPreNBA, Region::kNBA,
                                    Region::kPostNBA};
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    bool listed = kListed.count(r) != 0;
    EXPECT_EQ(IsActiveRegionSet(r), listed)
        << "Region index " << i
        << " misclassified by IsActiveRegionSet (expected " << listed << ")";
  }
}

// §4.4.1 ¶1: same membership rule, observed behaviorally. Scheduling one event
// in each of the five active region set regions and calling Run() exercises
// Scheduler::ExecuteActiveRegions, which uses IsActiveRegionSet to decide
// which regions belong to the active set drain. Capturing the CurrentRegion
// reported by each callback observes that production code routed exactly the
// five §4.4.1 ¶1 regions through the active-set drain path.
TEST(ActiveRegionSetSim, SchedulerDrainsAllFiveActiveRegionSetMembers) {
  Arena arena;
  Scheduler sched(arena);
  std::set<Region> observed;

  for (Region r : {Region::kActive, Region::kInactive, Region::kPreNBA,
                   Region::kNBA, Region::kPostNBA}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&, r]() {
      observed.insert(sched.CurrentRegion());
      EXPECT_EQ(sched.CurrentRegion(), r);
    };
    sched.ScheduleEvent({0}, r, ev);
  }
  sched.Run();
  EXPECT_EQ(observed.size(), 5u);
  EXPECT_TRUE(observed.count(Region::kActive));
  EXPECT_TRUE(observed.count(Region::kInactive));
  EXPECT_TRUE(observed.count(Region::kPreNBA));
  EXPECT_TRUE(observed.count(Region::kNBA));
  EXPECT_TRUE(observed.count(Region::kPostNBA));
}

// §4.4.1 ¶1: "Events scheduled in the Reactive, Re-Inactive, Pre-Re-NBA,
// Re-NBA, and Post-Re-NBA regions are reactive region set events." Same
// shape as the active-set predicate test, but for the five reactive-set
// members. Walking all 17 regions ensures the predicate accepts exactly the
// listed five and rejects the remaining twelve.
TEST(ReactiveRegionSetSim,
     ReactiveRegionSetPredicateAcceptsExactlyTheFiveListedRegions) {
  const std::set<Region> kListed = {Region::kReactive, Region::kReInactive,
                                    Region::kPreReNBA, Region::kReNBA,
                                    Region::kPostReNBA};
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    bool listed = kListed.count(r) != 0;
    EXPECT_EQ(IsReactiveRegionSet(r), listed)
        << "Region index " << i
        << " misclassified by IsReactiveRegionSet (expected " << listed << ")";
  }
}

// §4.4.1 ¶1 reactive-set membership, observed behaviorally. Scheduling one
// event in each of the five reactive region set regions exercises
// Scheduler::ExecuteReactiveRegions, which uses IsReactiveRegionSet to gate
// the reactive drain. Observing CurrentRegion from inside each callback
// confirms production routed each event through the reactive-set drain path.
TEST(ReactiveRegionSetSim, SchedulerDrainsAllFiveReactiveRegionSetMembers) {
  Arena arena;
  Scheduler sched(arena);
  std::set<Region> observed;

  for (Region r : {Region::kReactive, Region::kReInactive, Region::kPreReNBA,
                   Region::kReNBA, Region::kPostReNBA}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&, r]() {
      observed.insert(sched.CurrentRegion());
      EXPECT_EQ(sched.CurrentRegion(), r);
    };
    sched.ScheduleEvent({0}, r, ev);
  }
  sched.Run();
  EXPECT_EQ(observed.size(), 5u);
  EXPECT_TRUE(observed.count(Region::kReactive));
  EXPECT_TRUE(observed.count(Region::kReInactive));
  EXPECT_TRUE(observed.count(Region::kPreReNBA));
  EXPECT_TRUE(observed.count(Region::kReNBA));
  EXPECT_TRUE(observed.count(Region::kPostReNBA));
}

// §4.4.1 ¶1 disjointness: the LRM names two distinct groupings — active region
// set and reactive region set. The membership lists do not overlap. Production
// code must encode this disjointness so that ExecuteActiveRegions and
// ExecuteReactiveRegions drain disjoint queues; otherwise an event would be
// fired twice when both predicates fire. Walking all 17 regions and asserting
// the two predicates are never both true observes the disjointness rule on
// the production predicates.
TEST(RegionSetSim, ActiveAndReactiveRegionSetsAreDisjointAcrossAllRegions) {
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    EXPECT_FALSE(IsActiveRegionSet(r) && IsReactiveRegionSet(r))
        << "Region index " << i
        << " is in both the active and reactive region sets";
  }
}

// §4.4.1 ¶2: "The Active, Inactive, Pre-NBA, NBA, Post-NBA, Pre-Observed,
// Observed, Post-Observed, Reactive, Re-Inactive, Pre-Re-NBA, Re-NBA,
// Post-Re-NBA, and Pre-Postponed regions are known as the iterative regions."
// Production code expresses the rule through IsIterativeRegion, which the
// scheduler's outer iterate-while-non-empty loop reads via
// TimeSlot::AnyIterativeNonempty. Walking all 17 regions and asserting the
// predicate accepts exactly the fourteen listed — rejecting Preponed,
// Pre-Active, and Postponed — ties the §4.4.1 ¶2 list to the production
// classifier.
TEST(IterativeRegionsSim,
     IterativeRegionPredicateAcceptsExactlyTheFourteenListedRegions) {
  const std::set<Region> kListed = {
      Region::kActive,     Region::kInactive,     Region::kPreNBA,
      Region::kNBA,        Region::kPostNBA,      Region::kPreObserved,
      Region::kObserved,   Region::kPostObserved, Region::kReactive,
      Region::kReInactive, Region::kPreReNBA,     Region::kReNBA,
      Region::kPostReNBA,  Region::kPrePostponed};
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    bool listed = kListed.count(r) != 0;
    EXPECT_EQ(IsIterativeRegion(r), listed)
        << "Region index " << i
        << " misclassified by IsIterativeRegion (expected " << listed << ")";
  }
}

// §4.4.1 ¶2: the "iterative regions" label exists so the scheduler can loop
// over them until none holds an event — that loop is what makes a region
// iterative. The Pre-Postponed region is the most distinctive iterative
// region: it is non-iterative-looking by position (just before Postponed) yet
// LRM-classified as iterative. Scheduling an event into Pre-Postponed and
// observing that, from inside that callback, a freshly scheduled Active
// event fires within the same time slot proves the production loop in
// Scheduler::ExecuteTimeSlot routed Pre-Postponed through
// TimeSlot::AnyIterativeNonempty (which reads IsIterativeRegion) and then
// re-entered the active set drain. Without §4.4.1 ¶2 classifying
// Pre-Postponed as iterative the freshly scheduled Active event would never
// fire before Postponed runs.
TEST(IterativeRegionsSim,
     IterativeLoopReentersActiveSetAfterPrePostponedSchedulesActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<Region> sequence;

  auto* prepostponed = sched.GetEventPool().Acquire();
  prepostponed->callback = [&]() {
    sequence.push_back(sched.CurrentRegion());
    auto* active = sched.GetEventPool().Acquire();
    active->callback = [&]() { sequence.push_back(sched.CurrentRegion()); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, active);
  };
  sched.ScheduleEvent({0}, Region::kPrePostponed, prepostponed);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sequence.push_back(sched.CurrentRegion()); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  ASSERT_EQ(sequence.size(), 3u);
  EXPECT_EQ(sequence[0], Region::kPrePostponed);
  EXPECT_EQ(sequence[1], Region::kActive);
  EXPECT_EQ(sequence[2], Region::kPostponed);
}

// §4.4.1 ¶2: the iterative loop terminates only when no iterative region
// holds events. Postponed is NOT in the §4.4.1 ¶2 list, so events scheduled
// in Postponed must not keep the iterative loop alive — they fire only after
// the loop exits, in the post-loop Postponed drain. Without that exclusion,
// the loop would re-enter forever whenever Postponed had events. Scheduling
// an event in Postponed alongside one in Active and asserting both fire in
// the listed order observes that production code's IsIterativeRegion
// classifier correctly EXCLUDES Postponed.
TEST(IterativeRegionsSim,
     IterativeLoopExitsWhenOnlyNonIterativeRegionsHoldEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<Region> sequence;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { sequence.push_back(sched.CurrentRegion()); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sequence.push_back(sched.CurrentRegion()); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  ASSERT_EQ(sequence.size(), 2u);
  EXPECT_EQ(sequence[0], Region::kActive);
  EXPECT_EQ(sequence[1], Region::kPostponed);
}

// §4.4.1 ¶3: "all of the event regions of each time slot can be categorized
// as simulation regions (see 4.4.2) or PLI regions (see 4.4.3)." The
// normative content of ¶3 is the categorization's joint exhaustivity — every
// one of the 17 regions has at least one valid category. The specific
// membership of each category belongs to the descendant subclauses 4.4.2 and
// 4.4.3. Walking every region and asserting IsSimulationRegion(r) ||
// IsPliRegion(r) is true observes that production code's category predicates
// jointly cover all 17 regions, satisfying the §4.4.1 ¶3 existence rule.
TEST(RegionPartitionSim, EveryRegionIsCategorizedAsSimulationOrPliRegion) {
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    EXPECT_TRUE(IsSimulationRegion(r) || IsPliRegion(r))
        << "Region index " << i
        << " is in neither the simulation nor PLI category — §4.4.1 ¶3 "
           "requires every region to be categorizable as one of the two";
  }
}
