#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(PliPreponedSim, PreponedAccessesDataBeforeAnyStateChange) {
  Arena arena;
  Scheduler sched(arena);
  int value = 42;
  int sampled_in_preponed = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 100; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled_in_preponed = value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sampled_in_preponed, 42);
}

TEST(PliPreponedSim, PreponedSeesStateBeforeAllSimulationRegions) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto schedule_mod = [&](Region r, int new_val) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&value, new_val]() { value = new_val; };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule_mod(Region::kActive, 10);
  schedule_mod(Region::kInactive, 20);
  schedule_mod(Region::kNBA, 30);
  schedule_mod(Region::kReactive, 40);
  schedule_mod(Region::kReNBA, 50);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sampled, 0);
}

TEST(PliPreponedSim, PreponedExecutesBeforePreActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { order.push_back("pre_active"); };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { order.push_back("preponed"); };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "preponed");
  EXPECT_EQ(order[1], "pre_active");
}

TEST(PliPreponedSim, PreponedIsFirstRegionOrdinal) {
  EXPECT_EQ(static_cast<int>(Region::kPreponed), 0);
}

TEST(PliPreponedSim, PreponedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPreponedSim, PreponedSeesStatefromPreviousTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_t1 = -1;

  auto* active0 = sched.GetEventPool().Acquire();
  active0->callback = [&]() { value = 77; };
  sched.ScheduleEvent({0}, Region::kActive, active0);

  auto* preponed1 = sched.GetEventPool().Acquire();
  preponed1->callback = [&]() { sampled_t1 = value; };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed1);

  sched.Run();
  EXPECT_EQ(sampled_t1, 77);
}

TEST(PliPreponedSim, PreponedExecutesBeforeAllOtherRegions) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kPreponed, "preponed", order);

  sched.Run();
  ASSERT_GE(order.size(), 5u);
  EXPECT_EQ(order[0], "preponed");
}

TEST(PliPreponedSim, PreponedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreponed, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(PliPreponedSim, PreponedProvidesConsistentReadOnlySnapshot) {
  Arena arena;
  Scheduler sched(arena);
  int a = 1;
  int b = 2;
  int sum_in_preponed = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    a = 100;
    b = 200;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sum_in_preponed = a + b; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sum_in_preponed, 3);
}
