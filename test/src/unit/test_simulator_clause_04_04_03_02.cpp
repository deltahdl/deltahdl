#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(PliPreActiveSim, PreActiveRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPreActive, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(PliPreActiveSim, PreActiveCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 42;
  int sampled = -1;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreActive, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(PliPreActiveSim, PreActiveCanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_active = -1;

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { sampled_in_active = value; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(sampled_in_active, 99);
}

TEST(PliPreActiveSim, PreActiveCanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() {
    order.push_back("pre_active");

    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_active"); };
    sched.ScheduleEvent({0}, Region::kActive, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active");
  EXPECT_EQ(order[1], "created_active");
}

TEST(PliPreActiveSim, PreActiveExecutesBeforeActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { order.push_back("pre_active"); };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active");
  EXPECT_EQ(order[1], "active");
}

TEST(PliPreActiveSim, PreActiveExecutesAfterPreponedBeforeActive) {
  VerifyThreeRegionOrder({Region::kPreponed, "preponed"},
                         {Region::kPreActive, "pre_active"},
                         {Region::kActive, "active"});
}

TEST(PliPreActiveSim, PreActiveIsWithinActiveRegionSet) {
  auto pre_active_ord = static_cast<int>(Region::kPreActive);
  auto preponed_ord = static_cast<int>(Region::kPreponed);
  auto active_ord = static_cast<int>(Region::kActive);
  EXPECT_GT(pre_active_ord, preponed_ord);
  EXPECT_LT(pre_active_ord, active_ord);
}

TEST(PliPreActiveSim, PreActiveRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreActive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPreActiveSim, PreActiveEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(PliPreActiveSim, PreActiveReadWriteContrastWithPreponed) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int preponed_sample = -1;
  int active_sample = -1;

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { value = 55; };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { preponed_sample = value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { active_sample = value; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(preponed_sample, 0);
  EXPECT_EQ(active_sample, 55);
}
