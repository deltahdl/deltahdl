#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(ReactiveRegionSim, ReactiveSelfLoopSchedulesMoreReactiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    order.push_back(1);
    auto* next = sched.GetEventPool().Acquire();
    next->callback = [&order]() { order.push_back(2); };
    sched.ScheduleEvent({0}, Region::kReactive, next);
  };
  sched.ScheduleEvent({0}, Region::kReactive, ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

// §4.4.2.6 ¶1 sentence 1 edge case: "The Reactive region holds the current
// reactive region set events being evaluated...". When no events are
// scheduled into Reactive, the production drain
// Scheduler::ExecuteRegion(slot, Region::kReactive) finds an empty queue
// and returns immediately. The §4.4.2.6 "holds" rule degenerates to "holds
// zero events" without stalling the slot — observed by scheduling events
// only in regions other than Reactive and checking they still fire.
TEST(ReactiveRegionSim, ReactiveRegionEmptyDoesNotBlockOtherRegions) {
  Arena arena;
  Scheduler sched(arena);
  bool observed_fired = false;
  bool postponed_fired = false;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() { observed_fired = true; };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  auto* post = sched.GetEventPool().Acquire();
  post->callback = [&]() { postponed_fired = true; };
  sched.ScheduleEvent({0}, Region::kPostponed, post);

  sched.Run();
  EXPECT_TRUE(observed_fired);
  EXPECT_TRUE(postponed_fired);
}

TEST(ReactiveRegionSim, ReactiveExecutesBeforeReInactive) {
  VerifyTwoRegionOrder({Region::kReactive, "reactive"},
                       {Region::kReInactive, "reinactive"});
}

TEST(ReactiveRegionSim, ReactiveExecutesAfterObservedAndPostObserved) {
  VerifyThreeRegionOrder({Region::kObserved, "observed"},
                         {Region::kPostObserved, "post_observed"},
                         {Region::kReactive, "reactive"});
}

TEST(ReactiveRegionSim, ReactiveEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kReactive);
}

TEST(ReactiveRegionSim, ReactiveParticipatesInReNBAIteration) {
  VerifyIterationChain(Region::kReactive, "reactive", Region::kReNBA, "renba");
}

TEST(ReactiveRegionSim, ReactiveSchedulesActiveRestart) {
  VerifyRegionRestart({Region::kActive, "active1"},
                      {Region::kReactive, "reactive"},
                      {Region::kActive, "active2"});
}

// §4.4.2.6 ¶1 sentence 1: "The Reactive region holds the current reactive
// region set events being evaluated...". The Reactive callback observes
// Scheduler::CurrentRegion() while it runs: production ExecuteRegion sets
// current_region_ to kReactive before invoking the held event, so a callback
// scheduled into Reactive sees kReactive at the moment it executes. This
// pins the §4.4.2.6 "holds...being evaluated" claim to the production
// drain rather than relying on side effects in surrounding regions.
TEST(ReactiveRegionSim, CurrentRegionIsReactiveDuringReactiveEventEvaluation) {
  Arena arena;
  Scheduler sched(arena);
  Region observed = Region::kCOUNT;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, Region::kReactive, ev);

  sched.Run();
  EXPECT_EQ(observed, Region::kReactive);
}

// §4.4.2.6 ¶1 sentence 1: "...and can be processed in any order." The
// scheduler attests this latitude via the production-code predicate
// IsAnyOrderRegion, which returns true for Reactive. Every event scheduled
// into Reactive must still reach evaluation regardless of insertion order;
// each event tags itself with a unique id and the test asserts set-equality
// on the observed ids — the size check covers "holds" (no event dropped)
// and the set-membership check covers "any order" (no specific permutation
// required, no event repeated).
TEST(ReactiveRegionSim, ReactiveEventsAllProcessedAndAnyOrderIsAttested) {
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kReactive));

  Arena arena;
  Scheduler sched(arena);
  std::vector<int> observed;

  constexpr int kN = 5;
  for (int i = 0; i < kN; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&observed, i]() { observed.push_back(i); };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  sched.Run();
  ASSERT_EQ(observed.size(), static_cast<size_t>(kN));
  std::vector<bool> seen(kN, false);
  for (int id : observed) {
    ASSERT_GE(id, 0);
    ASSERT_LT(id, kN);
    EXPECT_FALSE(seen[id]) << "Reactive event id " << id << " seen twice";
    seen[id] = true;
  }
  for (int i = 0; i < kN; ++i) {
    EXPECT_TRUE(seen[i]) << "missing Reactive event id " << i;
  }
}

// §4.4.2.6 ¶2 sentence 1: "The code specified by blocking assignments in
// checkers, program blocks and the code in action blocks of concurrent
// assertions are scheduled in the Reactive region." All three
// §4.4.2.6-named sources funnel through one named production helper,
// Scheduler::HomeRegionForReactiveBlockingAssign(), which is the single
// routing site that applies the §4.4.2.6 ¶2 rule for every source it
// enumerates (the lowerer's program-block path already calls it;
// checker-body and concurrent-assertion lowering routes will call the
// same helper). The helper must report Region::kReactive and a callback
// scheduled there must fire during the Reactive drain — observed by
// CurrentRegion() reading kReactive at the moment the callback runs.
TEST(ReactiveRegionSim, ReactiveBlockingAssignAndActionHomeIsReactive) {
  EXPECT_EQ(Scheduler::HomeRegionForReactiveBlockingAssign(),
            Region::kReactive);

  Arena arena;
  Scheduler sched(arena);
  Region observed = Region::kCOUNT;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, Scheduler::HomeRegionForReactiveBlockingAssign(),
                      ev);

  sched.Run();
  EXPECT_EQ(observed, Region::kReactive);
}

// §4.4.2.6 ¶2 sentence 2: "The Reactive region is the reactive region set
// dual of the Active region (see 4.4.2.2)." The named production helper
// Scheduler::ReactiveSetDualOf maps the active anchor Region::kActive to
// its reactive-set counterpart Region::kReactive, codifying the §4.4.2.6
// dual as a one-to-one map between the two §4.4.2.2/§4.4.2.6 anchor
// regions. Any other input returns kCOUNT so the dual stays one-to-one.
// The classifier-symmetry check confirms each anchor sits in its set
// (Active in the active set, Reactive in the reactive set) and that both
// share the §4.7 any-order latitude, matching the §4.4.2.6 framing of the
// duality.
TEST(ReactiveRegionSim, ReactiveIsReactiveSetDualOfActive) {
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kActive), Region::kReactive);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kReactive), Region::kCOUNT);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kNBA), Region::kCOUNT);

  EXPECT_TRUE(IsActiveRegionSet(Region::kActive));
  EXPECT_TRUE(IsReactiveRegionSet(Region::kReactive));
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kActive));
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kReactive));
}
