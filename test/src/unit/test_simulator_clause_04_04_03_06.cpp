#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(PliPostObservedSim, PostObservedRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPostObserved, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(PliPostObservedSim, PostObservedCanReadValues) {
  VerifyRegionCanReadActiveValue(Region::kPostObserved);
}

TEST(PliPostObservedSim, PostObservedReadsAfterObservedRegion) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { value = 77; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostObserved, ev);

  sched.Run();
  EXPECT_EQ(sampled, 77);
}

TEST(PliPostObservedSim, PostObservedExecutesAfterObservedBeforeReactive) {
  VerifyThreeRegionOrder({Region::kObserved, "observed"},
                         {Region::kPostObserved, "post_observed"},
                         {Region::kReactive, "reactive"});
}

TEST(PliPostObservedSim, PostObservedExecutesAfterEntireChainThroughObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostObserved, "post_observed", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kPreObserved, "pre_observed", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_observed");
  EXPECT_EQ(order[2], "observed");
  EXPECT_EQ(order[3], "post_observed");
}

TEST(PliPostObservedSim, PostObservedIsAfterObservedBeforeReactive) {
  auto post_observed_ord = static_cast<int>(Region::kPostObserved);
  auto observed_ord = static_cast<int>(Region::kObserved);
  auto reactive_ord = static_cast<int>(Region::kReactive);
  EXPECT_GT(post_observed_ord, observed_ord);
  EXPECT_LT(post_observed_ord, reactive_ord);
}

TEST(PliPostObservedSim, PostObservedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostObserved, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPostObservedSim, PostObservedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPostObserved, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(PliPostObservedSim, PostObservedProvidesReadOnlySnapshotAfterObserved) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int sum_in_post_observed = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    a = 10;
    b = 20;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { b = 30; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  auto* post_obs = sched.GetEventPool().Acquire();
  post_obs->callback = [&]() { sum_in_post_observed = a + b; };
  sched.ScheduleEvent({0}, Region::kPostObserved, post_obs);

  sched.Run();
  EXPECT_EQ(sum_in_post_observed, 40);
}

TEST(PliPostObservedSim, PostObservedInfrastructureWorksEvenIfCurrentlyUnused) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kPostObserved, "post_observed", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kPreObserved, "pre_observed", order);
  ScheduleLabeled(sched, Region::kPostNBA, "post_nba", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);

  sched.Run();
  std::vector<std::string> expected = {"active",        "post_nba",
                                       "pre_observed",  "observed",
                                       "post_observed", "reactive"};
  EXPECT_EQ(order, expected);
}
