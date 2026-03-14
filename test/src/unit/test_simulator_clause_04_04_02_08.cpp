#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(ReNbaRegionSim, ReNBARegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kReNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(ReNbaRegionSim, ReNBAExecutesAfterReInactive) {
  VerifyTwoRegionOrder({Region::kReInactive, "reinactive"},
                       {Region::kReNBA, "renba"});
}

TEST(ReNbaRegionSim, AllReInactiveEventsCompleteBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("reinactive" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kReInactive, ev);
  }

  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { order.push_back("renba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  EXPECT_EQ(order[3], "renba");
}

TEST(ReNbaRegionSim, NonblockingAssignmentSchedulesReNBACurrentTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");

    auto* renba = sched.GetEventPool().Acquire();
    renba->callback = [&order]() { order.push_back("renba"); };
    sched.ScheduleEvent({0}, Region::kReNBA, renba);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "renba");
}

TEST(ReNbaRegionSim, NonblockingAssignmentSchedulesReNBALaterTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> renba_times;

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    auto* renba = sched.GetEventPool().Acquire();
    renba->callback = [&renba_times, &sched]() {
      renba_times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({5}, Region::kReNBA, renba);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(renba_times.size(), 1u);
  EXPECT_EQ(renba_times[0], 5u);
}

TEST(ReNbaRegionSim, ReNBAToReactiveIteration) {
  VerifyIterationChain(Region::kReactive, "reactive", Region::kReNBA, "renba");
}

TEST(ReNbaRegionSim, ReNBAExecutesAfterReactiveAndReInactiveBeforePostReNBA) {
  VerifyFourRegionOrder(
      {Region::kReactive, "reactive"}, {Region::kReInactive, "reinactive"},
      {Region::kReNBA, "renba"}, {Region::kPostReNBA, "post_renba"});
}

TEST(ReNbaRegionSim, ReNBAIsWithinReactiveRegionSet) {
  auto renba_ord = static_cast<int>(Region::kReNBA);
  auto reinactive_ord = static_cast<int>(Region::kReInactive);
  auto post_renba_ord = static_cast<int>(Region::kPostReNBA);
  EXPECT_GT(renba_ord, reinactive_ord);
  EXPECT_LT(renba_ord, post_renba_ord);
}

TEST(ReNbaRegionSim, ReNBAEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kReNBA);
}

TEST(ReNbaRegionSim, ReNBARegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}
