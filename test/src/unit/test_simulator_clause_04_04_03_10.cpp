#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(PliPostponedSim, PostponedCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(PliPostponedSim, PostponedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPostponedSim, PostponedEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kPostponed);
}

TEST(PliPostponedSim, PostponedInfrastructureWithFullRegionChain) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kPrePostponed, "pre_postponed", order);
  ScheduleLabeled(sched, Region::kPostReNBA, "post_re_nba", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kPostObserved, "post_observed", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kPostNBA, "post_nba", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kPreponed, "preponed", order);

  sched.Run();
  std::vector<std::string> expected = {
      "preponed", "active",      "post_nba",      "observed", "post_observed",
      "reactive", "post_re_nba", "pre_postponed", "postponed"};
  EXPECT_EQ(order, expected);
}
