#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh4426, ReactiveRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kReactive, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(SimCh4426, ReactiveRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(SimCh4426, ReactiveEventsProcessedInAnyValidOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 4; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  std::vector<int> sorted = order;
  std::sort(sorted.begin(), sorted.end());
  EXPECT_EQ(sorted, (std::vector<int>{0, 1, 2, 3}));
}

TEST(SimCh4426, ReactiveSelfLoopSchedulesMoreReactiveEvents) {
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

TEST(SimCh4426, ReactiveExecutesBeforeReInactive) {
  VerifyTwoRegionOrder({Region::kReactive, "reactive"},
                       {Region::kReInactive, "reinactive"});
}

TEST(SimCh4426, ReactiveIsWithinReactiveRegionSet) {
  auto reactive_ord = static_cast<int>(Region::kReactive);
  auto post_observed_ord = static_cast<int>(Region::kPostObserved);
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  EXPECT_GT(reactive_ord, post_observed_ord);
  EXPECT_LT(reactive_ord, pre_postponed_ord);
}

TEST(SimCh4426, ReactiveExecutesAfterObservedAndPostObserved) {
  VerifyThreeRegionOrder({Region::kObserved, "observed"},
                         {Region::kPostObserved, "post_observed"},
                         {Region::kReactive, "reactive"});
}

TEST(SimCh4426, ReactiveEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kReactive);
}

TEST(SimCh4426, ReactiveParticipatesInReNBAIteration) {
  VerifyIterationChain(Region::kReactive, "reactive", Region::kReNBA, "renba");
}

TEST(SimCh4426, ReactiveSchedulesActiveRestart) {
  VerifyRegionRestart({Region::kActive, "active1"},
                      {Region::kReactive, "reactive"},
                      {Region::kActive, "active2"});
}
