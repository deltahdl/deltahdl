#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(PliPreReNbaSim, PreReNBACanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreReNBA, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(PliPreReNbaSim, PreReNBACanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_re_nba = -1;

  auto* pre_re_nba = sched.GetEventPool().Acquire();
  pre_re_nba->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPreReNBA, pre_re_nba);

  auto* re_nba = sched.GetEventPool().Acquire();
  re_nba->callback = [&]() { sampled_in_re_nba = value; };
  sched.ScheduleEvent({0}, Region::kReNBA, re_nba);

  sched.Run();
  EXPECT_EQ(sampled_in_re_nba, 99);
}

TEST(PliPreReNbaSim, PreReNBACanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_re_nba = sched.GetEventPool().Acquire();
  pre_re_nba->callback = [&]() {
    order.push_back("pre_re_nba");

    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_re_nba"); };
    sched.ScheduleEvent({0}, Region::kReNBA, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPreReNBA, pre_re_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_re_nba");
  EXPECT_EQ(order[1], "created_re_nba");
}

TEST(PliPreReNbaSim, PreReNBAExecutesAfterReInactiveBeforeReNBA) {
  VerifyThreeRegionOrder({Region::kReInactive, "re_inactive"},
                         {Region::kPreReNBA, "pre_re_nba"},
                         {Region::kReNBA, "re_nba"});
}

TEST(PliPreReNbaSim, PreReNBAIsWithinReactiveRegionSet) {
  auto pre_re_nba_ord = static_cast<int>(Region::kPreReNBA);
  auto re_inactive_ord = static_cast<int>(Region::kReInactive);
  auto re_nba_ord = static_cast<int>(Region::kReNBA);
  EXPECT_GT(pre_re_nba_ord, re_inactive_ord);
  EXPECT_LT(pre_re_nba_ord, re_nba_ord);
}

TEST(PliPreReNbaSim, PreReNBARegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreReNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPreReNbaSim, PreReNBAEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreReNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(PliPreReNbaSim, PreReNBAReadWriteInReactiveRegionSetContext) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int reactive_sample = -1;
  int re_nba_sample = -1;

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  auto* pre_re_nba = sched.GetEventPool().Acquire();
  pre_re_nba->callback = [&]() {
    reactive_sample = value;
    value = 55;
  };
  sched.ScheduleEvent({0}, Region::kPreReNBA, pre_re_nba);

  auto* re_nba = sched.GetEventPool().Acquire();
  re_nba->callback = [&]() { re_nba_sample = value; };
  sched.ScheduleEvent({0}, Region::kReNBA, re_nba);

  sched.Run();
  EXPECT_EQ(reactive_sample, 10);
  EXPECT_EQ(re_nba_sample, 55);
}
