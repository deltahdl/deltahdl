#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(PliPreNbaSim, PreNBARegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPreNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(PliPreNbaSim, PreNBACanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 42;
  int sampled = -1;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreNBA, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(PliPreNbaSim, PreNBACanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_nba = -1;

  auto* pre_nba = sched.GetEventPool().Acquire();
  pre_nba->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre_nba);

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { sampled_in_nba = value; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  EXPECT_EQ(sampled_in_nba, 99);
}

TEST(PliPreNbaSim, PreNBACanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_nba = sched.GetEventPool().Acquire();
  pre_nba->callback = [&]() {
    order.push_back("pre_nba");

    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_nba"); };
    sched.ScheduleEvent({0}, Region::kNBA, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_nba");
  EXPECT_EQ(order[1], "created_nba");
}

TEST(PliPreNbaSim, PreNBAExecutesBeforeNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* pre_nba = sched.GetEventPool().Acquire();
  pre_nba->callback = [&]() { order.push_back("pre_nba"); };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_nba");
  EXPECT_EQ(order[1], "nba");
}

TEST(PliPreNbaSim, PreNBAExecutesAfterInactiveBeforeNBA) {
  VerifyThreeRegionOrder({Region::kInactive, "inactive"},
                         {Region::kPreNBA, "pre_nba"}, {Region::kNBA, "nba"});
}

TEST(PliPreNbaSim, PreNBAIsWithinActiveRegionSet) {
  auto pre_nba_ord = static_cast<int>(Region::kPreNBA);
  auto inactive_ord = static_cast<int>(Region::kInactive);
  auto nba_ord = static_cast<int>(Region::kNBA);
  EXPECT_GT(pre_nba_ord, inactive_ord);
  EXPECT_LT(pre_nba_ord, nba_ord);
}

TEST(PliPreNbaSim, PreNBARegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPreNbaSim, PreNBAEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(PliPreNbaSim, PreNBAReadWriteInActiveRegionSetContext) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int active_sample = -1;
  int nba_sample = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* pre_nba = sched.GetEventPool().Acquire();
  pre_nba->callback = [&]() {
    active_sample = value;
    value = 55;
  };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre_nba);

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { nba_sample = value; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  EXPECT_EQ(active_sample, 10);
  EXPECT_EQ(nba_sample, 55);
}
