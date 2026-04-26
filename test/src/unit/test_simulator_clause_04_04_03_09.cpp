#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(PliPrePostponedSim, PrePostponedRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(PliPrePostponedSim, PrePostponedCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(PliPrePostponedSim, PrePostponedCanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_postponed = -1;

  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sampled_in_postponed = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sampled_in_postponed, 99);
}

TEST(PliPrePostponedSim, PrePostponedCanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() {
    order.push_back("pre_postponed");

    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_postponed"); };
    sched.ScheduleEvent({0}, Region::kPostponed, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_postponed");
  EXPECT_EQ(order[1], "created_postponed");
}

TEST(PliPrePostponedSim, PrePostponedExecutesAfterPostReNBABeforePostponed) {
  VerifyThreeRegionOrder({Region::kPostReNBA, "post_re_nba"},
                         {Region::kPrePostponed, "pre_postponed"},
                         {Region::kPostponed, "postponed"});
}

TEST(PliPrePostponedSim, PrePostponedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPrePostponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPrePostponedSim, PrePostponedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPrePostponed, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}
