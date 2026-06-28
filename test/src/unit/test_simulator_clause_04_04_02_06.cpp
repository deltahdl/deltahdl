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

TEST(ReactiveRegionSim, ReactiveIsReactiveSetDualOfActive) {
  // §4.4.2.6/§4.4.2.7/§4.4.2.8: the reactive region set mirrors the active set
  // — Reactive is the dual of Active, Re-Inactive of Inactive, and Re-NBA of
  // NBA. A region that is not itself an active-set member (e.g. Reactive) has
  // no dual.
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kActive), Region::kReactive);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kInactive),
            Region::kReInactive);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kNBA), Region::kReNBA);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kReactive), Region::kCOUNT);

  EXPECT_TRUE(IsActiveRegionSet(Region::kActive));
  EXPECT_TRUE(IsReactiveRegionSet(Region::kReactive));
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kActive));
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kReactive));
}
