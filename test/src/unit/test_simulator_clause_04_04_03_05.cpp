#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh4435, PreObservedRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPreObserved, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(SimCh4435, PreObservedCanReadValues) {
  VerifyRegionCanReadActiveValue(Region::kPreObserved);
}

TEST(SimCh4435, PreObservedReadsAfterActiveRegionSetStabilized) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() { value = 77; };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreObserved, ev);

  sched.Run();
  EXPECT_EQ(sampled, 77);
}

TEST(SimCh4435, PreObservedExecutesAfterPostNBABeforeObserved) {
  VerifyThreeRegionOrder({Region::kPostNBA, "post_nba"},
                         {Region::kPreObserved, "pre_observed"},
                         {Region::kObserved, "observed"});
}

TEST(SimCh4435, PreObservedExecutesAfterEntireActiveRegionSet) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPreObserved, "pre_observed", order);
  ScheduleLabeled(sched, Region::kPostNBA, "post_nba", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
  EXPECT_EQ(order[2], "post_nba");
  EXPECT_EQ(order[3], "pre_observed");
}

TEST(SimCh4435, PreObservedIsAfterPostNBABeforeObserved) {
  auto pre_observed_ord = static_cast<int>(Region::kPreObserved);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  auto observed_ord = static_cast<int>(Region::kObserved);
  EXPECT_GT(pre_observed_ord, post_nba_ord);
  EXPECT_LT(pre_observed_ord, observed_ord);
}

TEST(SimCh4435, PreObservedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreObserved, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(SimCh4435, PreObservedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreObserved, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(SimCh4435, PreObservedProvidesReadOnlySnapshotAfterActiveSet) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int sum_in_pre_observed = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    a = 10;
    b = 20;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() { sum_in_pre_observed = a + b; };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  EXPECT_EQ(sum_in_pre_observed, 30);
}

TEST(SimCh4435, PreObservedReadsFullyStabilizedActiveSetState) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto set_final = [&]() { value = 99; };
  auto schedule_reentry = [&]() {
    auto* active2 = sched.GetEventPool().Acquire();
    active2->callback = set_final;
    sched.ScheduleEvent({0}, Region::kActive, active2);
  };

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    if (value == 0) {
      value = 1;
      auto* inactive = sched.GetEventPool().Acquire();
      inactive->callback = schedule_reentry;
      sched.ScheduleEvent({0}, Region::kInactive, inactive);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  EXPECT_EQ(sampled, 99);
}
