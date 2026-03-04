#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh4434, PostNBARegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPostNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(SimCh4434, PostNBACanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostNBA, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(SimCh4434, PostNBACanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_observed = -1;

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { sampled_in_observed = value; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  sched.Run();
  EXPECT_EQ(sampled_in_observed, 99);
}

TEST(SimCh4434, PostNBACanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() {
    order.push_back("post_nba");

    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_observed"); };
    sched.ScheduleEvent({0}, Region::kObserved, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "post_nba");
  EXPECT_EQ(order[1], "created_observed");
}

TEST(SimCh4434, PostNBAExecutesAfterNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() { order.push_back("post_nba"); };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "nba");
  EXPECT_EQ(order[1], "post_nba");
}

TEST(SimCh4434, PostNBAExecutesAfterNBABeforePreObserved) {
  VerifyThreeRegionOrder({Region::kNBA, "nba"}, {Region::kPostNBA, "post_nba"},
                         {Region::kPreObserved, "pre_observed"});
}

TEST(SimCh4434, PostNBAIsWithinActiveRegionSet) {
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  auto nba_ord = static_cast<int>(Region::kNBA);
  auto pre_observed_ord = static_cast<int>(Region::kPreObserved);
  EXPECT_GT(post_nba_ord, nba_ord);
  EXPECT_LT(post_nba_ord, pre_observed_ord);
}

TEST(SimCh4434, PostNBARegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(SimCh4434, PostNBAEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPostNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(SimCh4434, PostNBAReadWriteInActiveRegionSetContext) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int nba_sample = -1;
  int observed_sample = -1;

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() {
    nba_sample = value;
    value = 55;
  };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { observed_sample = value; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  sched.Run();
  EXPECT_EQ(nba_sample, 10);
  EXPECT_EQ(observed_sample, 55);
}
