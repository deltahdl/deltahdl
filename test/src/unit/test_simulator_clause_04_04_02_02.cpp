#include <gtest/gtest.h>

#include <set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

// §4.4.2.2: the Active region "holds the current active region set events
// being evaluated...and can be processed in any order." The LRM grants the
// implementation freedom over the intra-Active ordering; the testable rule
// is that every event scheduled into Active reaches evaluation, with no drop
// or duplicate, regardless of insertion order. Each event tags itself with a
// unique id so the test asserts set-equality on the observed ids — the size
// check covers "holds" (all events visited) and the set-membership check
// covers "any order" (no specific permutation required, but no event lost or
// repeated). Run() drives Scheduler::ExecuteRegion(slot, Region::kActive),
// which is the production drain under observation.
TEST(ActiveRegionSim, ActiveRegionEventsAllProcessedRegardlessOfOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> observed;

  constexpr int kN = 5;
  for (int i = 0; i < kN; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&observed, i]() { observed.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(observed.size(), static_cast<size_t>(kN));
  std::set<int> seen(observed.begin(), observed.end());
  EXPECT_EQ(seen.size(), static_cast<size_t>(kN));
  for (int i = 0; i < kN; ++i) {
    EXPECT_TRUE(seen.count(i)) << "missing Active event id " << i;
  }
}

// §4.4.2.2: events "being evaluated" means the Active region is the
// evaluation site for active-set work. Scheduler::CurrentRegion() must report
// kActive while an Active event's callback runs — this is what production
// code (e.g. NoteWriteAttempt's Preponed/Postponed checks) keys off to apply
// region-specific rules. Observing kActive from inside the callback confirms
// ExecuteRegion sets the current region before invoking the held event.
TEST(ActiveRegionSim, CurrentRegionIsActiveDuringActiveEventEvaluation) {
  Arena arena;
  Scheduler sched(arena);
  Region observed = Region::kCOUNT;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(observed, Region::kActive);
}

// §4.4.2.2 edge case: when no events are scheduled into the Active region,
// the production drain Scheduler::ExecuteRegion(slot, Region::kActive) finds
// an empty queue and returns immediately. The downstream regions still run
// for the same slot. Observing a non-Active event fire in a slot whose Active
// queue is empty proves the empty-Active path is non-blocking — the "holds"
// rule degenerates to "holds zero events" without stalling the slot.
TEST(ActiveRegionSim, ActiveRegionEmptyDoesNotBlockOtherRegions) {
  Arena arena;
  Scheduler sched(arena);
  bool inactive_fired = false;
  bool postponed_fired = false;

  auto* inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() { inactive_fired = true; };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { postponed_fired = true; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_TRUE(inactive_fired);
  EXPECT_TRUE(postponed_fired);
}

// §4.4.2.2 cross-references §4.4.1: it says the Active region "holds the
// current active region set events". The phrase "active region set events"
// is defined by §4.4.1 ¶1 — events scheduled in Active, Inactive, Pre-NBA,
// NBA, and Post-NBA. Production code IsActiveRegionSet(Region::kActive)
// must therefore return true; otherwise §4.4.2.2's claim that the Active
// region holds active-set events would be a free-floating cross-reference.
// Routing through the §4.4.1 classifier here makes the §4.4.2.2 ↔ §4.4.1
// cycle relationship observable at the §4.4.2.2 level, so a regression in
// §4.4.1's classifier would surface as a §4.4.2.2 failure too.
TEST(ActiveRegionSim, ActiveRegionIsActiveRegionSetMember) {
  EXPECT_TRUE(IsActiveRegionSet(Region::kActive));
}

// §4.4.2.2: "...holds the current active region set events being evaluated".
// "Being evaluated" includes events scheduled into Active by an in-flight
// Active callback at the current time — they enter the same Active queue
// while it is still being drained. Production Scheduler::DrainQueue loops on
// queue.empty() so a push during a callback is picked up in the same drain.
// Observing the dynamically-added event's callback fire confirms the Active
// region holds events added mid-evaluation, not only those scheduled before
// Run() begins.
TEST(ActiveRegionSim, ActiveRegionHoldsEventsScheduledDuringActiveEvaluation) {
  Arena arena;
  Scheduler sched(arena);
  bool outer_fired = false;
  bool inner_fired = false;

  auto* outer = sched.GetEventPool().Acquire();
  outer->callback = [&]() {
    outer_fired = true;
    auto* inner = sched.GetEventPool().Acquire();
    inner->callback = [&]() { inner_fired = true; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, inner);
  };
  sched.ScheduleEvent({0}, Region::kActive, outer);

  sched.Run();
  EXPECT_TRUE(outer_fired);
  EXPECT_TRUE(inner_fired);
}
